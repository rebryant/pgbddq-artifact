/************************************************************************************[qrat-trim.c]
Copyright (c) 2014, Marijn Heule and Nathan Wetzler
Copyright (c) 2019-2020 Marijn Heule, Carnegie Mellon University
Last edit, October 1, 2020

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>

#define TIMEOUT     900
#define BIGINIT     1000000
#define INIT        8
#define END         0
#define UNSAT       0
#define SAT         1
#define EXTRA       5
#define INFOBITS    2
#define MARK        3
#define ERROR      -1
#define ACTIVE      1
#define ID         -1
#define PIVOT      -2
#define OUTER      -3
#define LEVEL      -4

#define BLUEVERSION

#define FORWARD_SAT      10
#define FORWARD_UNSAT    20
#define BACKWARD_UNSAT   30
#define SUCCEED          40
#define FAILED           50

#define QBF
#ifdef QBF
  #define UNIVERSAL   2
#endif

#define OUTER_INIT_SIZE            1000000
#define CANDIDATE_INIT_SIZE        10
#define RAT_DEPENDENCIES_INIT_SIZE 10

struct solver { FILE *inputFile, *proofFile, *coreFile, *aigFile, *lemmaFile, *skolemFile, *traceFile;
    int *DB, nVars, timeout, mask, delete, *falseStack, *false, *forced,
      *processed, *assigned, count, *used, *max, *delinfo, RATmode, RATcount, REDcount,
      Lcount, maxCandidates, *resolutionCandidates, maxRATdependencies, currentRATdependencies,
      *RATdependencies, maxVar, mode, verb, unitSize;
#ifdef BLUEVERSION
    int inneronly, innerpassed, innerfailed, outerrequired;
    int *outer, outerSize, outerAlloc;
#endif
#ifdef QBF
    int *level, *levelOcc, maxLevel, *rep, *Skolem;
#endif
    struct timeval start_time;
    long mem_used, time, nClauses, lastLemma, *unitStack, *reason, lemmas, arcs, *adlist, **wlist;  };

#define ASSIGN(a)	{ S->false[-(a)] = 1; *(S->assigned++) = -(a); }
#define ADD_WATCH(l,m)  { if (S->used[(l)] + 1 == S->max[(l)]) { S->max[(l)] *= 1.5; \
                            S->wlist[(l)] = (long *) realloc(S->wlist[(l)], sizeof(long) * S->max[(l)]); } \
                          S->wlist[(l)][ S->used[(l)]++ ] = (m); S->wlist[(l)][ S->used[(l)] ] = END; }

static inline void printClause(int* clause) {
  printf("[%i] (%i) : ", clause[ID], clause[PIVOT]);
  while(*clause) printf("%i ", *clause++); printf("0\n"); }

static inline void addWatch (struct solver* S, int* clause, int index) {
  int lit = clause[ index ];
  if (S->used[lit] + 1 == S->max[lit]) { S->max[lit] *= 1.5;
    S->wlist[lit] = (long*) realloc(S->wlist[lit], sizeof(long) * S->max[lit]); }
  S->wlist[lit][ S->used[lit]++ ] = ((long) (((clause) - S->DB)) << 1) + S->mask;
  S->wlist[lit][ S->used[lit]   ] = END; }

static inline void removeWatch (struct solver* S, int* clause, int index) {
  int lit = clause[index]; long *watch = S->wlist[lit];
  for (;;) {
    int* _clause = S->DB + (*(watch++) >> 1);
    if (_clause == clause) {
      watch[-1] = S->wlist[lit][ --S->used[lit] ];
      S->wlist[lit][ S->used[lit] ] = END; return; } } }

static inline void addUnit (struct solver* S, long index) {
  S->unitStack[ S->unitSize++ ] = index; }

static inline void removeUnit (struct solver* S, int lit) {
  int i, found = 0;
  for (i = 0; i < S->unitSize; i++) {
    if (found) S->unitStack[i - 1] = S->unitStack[i];
    if (S->DB[ S->unitStack[i] ] == lit) found = 1; }
  S->unitSize--; }

static inline void unassignUnit (struct solver* S, int lit) {
  if (S->verb)
    printf("c removing unit %i\n", lit);
  while (S->false[-lit]) {
    if (S->verb)
      printf("c removing unit %i (%i)\n", S->forced[-1], lit);
    S->false[*(--S->forced)] = 0; }
  S->processed = S->assigned = S->forced; }

static inline void markWatch (struct solver* S, int* clause, int index, int offset) {
  long* watch = S->wlist[ clause[ index ] ];
  for (;;) {
    int *_clause = (S->DB + (*(watch++) >> 1) + (long) offset);
    if (_clause == clause) { watch[-1] |= ACTIVE; return; } } }

static inline void markClause (struct solver* S, int* clause, int index) {
  S->arcs++;

  if (S->traceFile) {
    if (S->RATmode) {
      if (S->currentRATdependencies == S->maxRATdependencies) {
        S->maxRATdependencies = (S->maxRATdependencies * 3) >> 1;
        S->RATdependencies = realloc(S->RATdependencies, sizeof(int) * S->maxRATdependencies); }
      S->RATdependencies[S->currentRATdependencies] = clause[index - 1] >> 1;
      S->currentRATdependencies++; }
    else fprintf(S->traceFile, "%i ", clause[index - 1] >> 1); }

  if ((clause[index - 1] & ACTIVE) == 0) {
    clause[index - 1] |= ACTIVE;
    if (S->lemmaFile && clause[1])
      *(S->delinfo++) = (((int) (clause - S->DB) + index) << 1) + 1;
    if (clause[1 + index] == 0) return;
    markWatch (S, clause,     index, -index);
    markWatch (S, clause, 1 + index, -index); }
  while (*clause) S->false[ *(clause++) ] = MARK; }

void analyze (struct solver* S, int* clause, int index) {     // Mark all clauses involved in conflict
  markClause (S, clause, index);
  while (S->assigned > S->falseStack) {
    int lit = *(--S->assigned);
    if ((S->false[ lit ] == MARK) &&
        (S->reason[ abs(lit) ]) ) {
      markClause (S, S->DB+S->reason[ abs(lit) ], -1);
      if (S->assigned >= S->forced)
        S->reason[ abs(lit) ] = 0; }
    S->false[ lit ] = (S->assigned < S->forced); }

  if (S->traceFile && !S->RATmode) fprintf (S->traceFile, "0\n");  // preferably elsewhere
  S->processed = S->assigned = S->forced; }

int propagate (struct solver* S, int init) {        // Performs unit propagation
  int *start[2], check = 0;
  int i, lit, _lit = 0; long *watch, *_watch;
  start[0] = start[1] = S->processed;
  flip_check:;
  check ^= 1;
  while (start[check] < S->assigned) {              // While unprocessed false literals
    lit = *(start[check]++);                        // Get first unprocessed literal
//    printf("propagate %i\n", lit);
#ifdef QBF
    if (init && S->level[abs(lit)] % 2) {           // only for QBF
      int *reason = S->DB + S->reason[abs(lit)];
      if (reason) analyze (S, reason, -1);
      return UNSAT; }
#endif
    if (lit == _lit) watch = _watch;
    else watch = S->wlist[ lit ];                   // Obtain the first watch pointer
    while (*watch != END) {                         // While there are watched clauses (watched by lit)
      if ((*watch & 1) != check) {
        watch++; continue; }
     int *clause = S->DB + (*watch >> 1);	    // Get the clause from DB
     if (S->false[ -clause[0] ] ||
         S->false[ -clause[1] ]) {
       watch++; continue; }
     if (clause[0] == lit) clause[0] = clause[1];   // Ensure that the other watched literal is in front
      for (i = 2; clause[i]; ++i)                   // Scan the non-watched literals
        if (S->false[ clause[i] ] == 0) {           // When clause[j] is not false, it is either true or unset
          clause[1] = clause[i]; clause[i] = lit;   // Swap literals
          ADD_WATCH (clause[1], *watch);            // Add the watch to the list of clause[1]
          *watch = S->wlist[lit][ --S->used[lit] ]; // Remove pointer
          S->wlist[lit][ S->used[lit] ] = END;
          goto next_clause; }                       // Goto the next watched clause
      clause[1] = lit; watch++;                     // Set lit at clause[1] and set next watch
      if (!S->false[  clause[0] ]) {                // If the other watched literal is falsified,
        ASSIGN (clause[0]);                         // A unit clause is found, and the reason is set
        S->reason[abs(clause[0])] = ((long) ((clause)-S->DB)) + 1;
        if (!check) {
          start[0]--; _lit = lit; _watch = watch;
          goto flip_check; } }
      else { analyze(S, clause, 0); return UNSAT; } // Found a root level conflict -> UNSAT
      next_clause: ; } }                            // Set position for next clause
  if (check) goto flip_check;
  S->processed = S->assigned;
  return SAT; }	                                    // Finally, no conflict was found

static inline int propagateUnits (struct solver* S, int init) {
  int i;
  while (S->forced > S->falseStack) { S->false[*(--S->forced)] = 0; }
  S->forced = S->assigned = S->processed = S->falseStack;
  for (i = 0; i < S->unitSize; i++) {
    int lit = S->DB[ S->unitStack[i] ];
//    if (S->false[-lit]) {
//      if (S->verb) printf("c unit %i is already assigned\n", lit);
//      continue; }
    S->reason[abs(lit)] = S->unitStack[i] + 1;
    ASSIGN (lit); }

  if (propagate (S, init) == UNSAT) { return UNSAT; }
  S->forced = S->processed;
  return SAT; }

// Put falsified literals at the end and returns the size under the current
// assignment: negative size means satisfied, size = 0 means falsified
int sortSize (struct solver *S, int *lemma, int diff) {
  unsigned int size = 0, last = 0, sat = 1;
  while (lemma[ last ]) {
    int lit = lemma[ last++ ];
#ifdef QBF
    S->levelOcc[ S->level[abs(lit)] ] += diff;
#endif
    if (S->false[ lit ] == 0) {
      if (S->false[ -lit ]) sat = -1;
      lemma[ last-1 ] = lemma[ size ];
      lemma[ size++ ] = lit; } }

  return sat * size; }

#ifdef QBF
int URcheck (struct solver *S, int other, int reslit) {
  int *clause = S->DB + (S->adlist[other] >> INFOBITS);
  if (S->verb) {
    printf("c UR marking clause "); printClause(clause); }
  clause[ID] |= ACTIVE;
  int thisLevel = S->level[abs(reslit)];
  if (S->level[abs(reslit)] % 2 == 0) return FAILED;
  while (*clause) {
//    printf ("c level[%i] = %i\n", *clause, S->level[abs(*clause)]);
    int level = S->level[abs(*clause++)];
    if (level > thisLevel && (level % 2 == 0)) return FAILED; }
  if (S->verb)
    printf("c lemma has EUR\n");
  return SUCCEED; }

int EURcheck (struct solver *S, int *clause, int reslit) {
  int i, j, max;

  int thisLevel = S->level[abs(reslit)];
  for (i = 1; i <= S->maxVar; i++) {
    if (S->level[i] > thisLevel) S->rep[i] = i;
    else                         S->rep[i] = 0; }

  for (i = -S->maxVar; i <= S->maxVar; i++) {
    if (i == 0) continue;
    // Loop over all watched clauses for literal
    for (j = 0; j < S->used[i]; j++) {
      int *watchp = S->DB + (S->wlist[i][j] >> 1);
      // If watched literal is in first position
      if (*watchp == i) {
        max = 0;
        int *c = watchp;
        while (*c) { int var = abs(*c++);
          if (S->rep[var] > max) max = S->rep[var]; }
        c = watchp;
        while (*c) { int var = abs(*c++);
          if (S->rep[var] != 0) S->rep[var] = max; } } } }

  max = 0;
  if (S->verb) printf("c REP: ");
  while (*clause) { int lit = *clause++;
    if (S->verb) printf("%i (%i) ", lit, S->rep[abs(lit)]);
    if (S->rep[abs(lit)] > max) max = S->rep[abs(lit)]; }
  if (S->verb) printf("\n");

  for (i = -S->maxVar; i <= S->maxVar; i++) {
    if (i == 0) continue;
    // Loop over all watched clauses for literal
    for (j = 0; j < S->used[i]; j++) {
      int* watchp = S->DB + (S->wlist[i][j] >> 1);
      // If watched literal is in first position
      if (*watchp == i) {
        int flag = 1;
        int *c = watchp;
        while (*c) if (*c++ == -reslit) flag = 0;
        if (flag) continue;

        if (S->verb) {
          printf("c EUR to check "); printClause (watchp); }
        while (*watchp)
          if (S->rep[abs(*watchp++)] == max) {
            printf("c EUR check FAILED\n");
            return FAILED; } } } }

  printf("c lemma has EUR\n");
  return SUCCEED; }
#endif

// print the core clauses to coreFile in DIMACS format
void printCore (struct solver *S) {
  if (S->mode == FORWARD_SAT) return;

  int i, j, count = 0;
  for (i = 0; i < S->nClauses; i++) {
    int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
    if (lemmas[ID] & ACTIVE) count++; }
  printf("c %i of %li clauses in core\n", count, S->nClauses);

  if (S->coreFile) {
    fprintf(S->coreFile, "p cnf %i %i\n", S->nVars, count);
#ifdef QBF
    for (i = 0; i <= S->maxLevel; i++) {
      if (i % 2) fprintf(S->coreFile, "a ");
      else       fprintf(S->coreFile, "e ");
      for (j = 1; j <= S->nVars; j++)
        if (S->level[j] == i) fprintf(S->coreFile, "%i ", j);
      fprintf(S->coreFile, "0\n"); }
#endif
    for (i = 0; i < S->nClauses; i++) {
      int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
      if (lemmas[ID] & ACTIVE) {
        while (*lemmas) fprintf(S->coreFile, "%i ", *lemmas++);
        fprintf(S->coreFile, "0\n"); } }
    fclose(S->coreFile); } }

// print the core lemmas to lemmaFile in QRAT format
void printProof (struct solver *S) {
  printf("c %i of %i lemmas in core using %lu resolution steps\n", S->REDcount + 1, S->Lcount, S->arcs);
  printf("c %d RAT lemmas in core\n", S->RATcount);

  if (S->lemmaFile) {
    S->delinfo--;
    while (*S->delinfo) {
      int offset = *S->delinfo--;
      if (offset & 1) fprintf (S->lemmaFile, "d ");
      int *lemmas = S->DB + (offset >> 1);
      // add something for universals
      int reslit = lemmas[PIVOT];
      fprintf (S->lemmaFile, "%i ", reslit);
      while (*lemmas) {
        int lit = *lemmas++;
        if (lit != reslit) fprintf (S->lemmaFile, "%i ", lit); }
      fprintf (S->lemmaFile, "0\n"); }
    fprintf (S->lemmaFile, "0\n");
    fclose (S->lemmaFile); } }

// print the dependency graph to traceFile in TraceCheck+ format
void printTrace (struct solver *S) {
  if (S->traceFile) { int i;
    for (i = 0; i < S->nClauses; i++) {
      int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
      if (lemmas[ID] & ACTIVE) {
        fprintf(S->traceFile, "%i ", i + 1);
        while (*lemmas) fprintf (S->traceFile, "%i ", *lemmas++);
        fprintf (S->traceFile, "0 0\n"); } }
    fclose (S->traceFile); } }

inline int map (int lit) {
  lit *= -1;
  if (lit > 0) return  2 * lit;
  else         return -2 * lit + 1; }

void printAND (struct solver *S, int lhs, int rhs0, int rhs1, int last) {
  if (rhs0 > 2 * last + 1) printf("ERROR %i\n", rhs0);
  if (rhs1 > 2 * last + 1) printf("ERROR %i\n", rhs1);

  if ((lhs % 2)) printf("c ERROR LHS is not even %i\n", lhs);
//  assert ((lhs % 2) == 0);

  if (S->aigFile) fprintf(S->aigFile, "%i %i %i\n", lhs, rhs0, rhs1);
  int max = 2 * S->maxVar + 1;

  if (lhs  >  max) lhs  += 2 * (int) S->nClauses;
  if (rhs0 >  max) rhs0 += 2 * (int) S->nClauses;
  if (rhs1 >  max) rhs1 += 2 * (int) S->nClauses;

  if (lhs  < -max) lhs  -= 2 * (int) S->nClauses;
  if (rhs0 < -max) rhs0 -= 2 * (int) S->nClauses;
  if (rhs1 < -max) rhs1 -= 2 * (int) S->nClauses;

  lhs = lhs / 2;
  if      (rhs0 == 0) rhs0 = -last;
  else if (rhs0 == 1) rhs0 =  last;
  else if (rhs0  % 2) rhs0 = -1 * (rhs0 / 2);
  else                rhs0 =  rhs0 / 2;
  if      (rhs1 == 0) rhs1 = -last;
  else if (rhs1 == 1) rhs1 =  last;
  else if (rhs1  % 2) rhs1 = -1 * (rhs1 / 2);
  else                rhs1 =  rhs1 / 2;

  if (S->skolemFile) {
    fprintf(S->skolemFile, "%i %i %i 0\n",  lhs, -rhs0, -rhs1);
    fprintf(S->skolemFile, "%i %i 0\n"   , -lhs, rhs0);
    fprintf(S->skolemFile, "%i %i 0\n"   , -lhs, rhs1); } }

int pureLiteralSubstitution (struct solver * S) {
  int i, *polarity, *unit;
  polarity = (int*) malloc (sizeof(int) * (S->maxVar + 1));
  unit     = (int*) malloc (sizeof(int) * (S->maxVar + 1));

  for (i = 1; i <= S->maxVar; i++) {
    polarity[i] = 0;
    unit    [i] = 0; }

  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[i];
    int pivot = clause[PIVOT];
    unit[abs(pivot)] = S->Skolem[i];
    if (polarity[abs(pivot)] ==   0  ) polarity[abs(pivot)] = pivot;
    if (polarity[abs(pivot)] != pivot) polarity[abs(pivot)] = S->maxVar + 1; }

  int j = 0;
  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[i];
    int pivot = clause[PIVOT];
    int flag  = 0;
    while (*clause) {
      if (polarity[abs(*clause)] == *clause) flag = 1;
      clause++; }
    if (flag) continue;
    clause = S->DB + S->Skolem[i];
    int *newclause = clause;
    while (*clause) {
      if (polarity[abs(*clause)] != -*clause)
        *newclause++ = *clause;
      clause++; }
    *newclause = 0;
    S->Skolem[j++] = S->Skolem[i]; }

  for (i = 1; i <= S->maxVar; i++)
    if (abs(polarity[i]) == i) {
      S->Skolem[j++]     = unit[i];
      S->DB[unit[i]    ] = S->DB[unit[i] + PIVOT];
      S->DB[unit[i] + 1] = 0; }

  free(unit);
  free(polarity);

  int result = S->RATcount - j;
  S->RATcount = j;

  return result; }

int replaceLastByUnit (struct solver *S) {
  int i, *polarity, _RATcount = S->RATcount;
  polarity = (int*) malloc (sizeof(int) * (S->maxVar + 1));

  for (i = 1; i <= S->maxVar; i++)
    polarity[i] =  0;

  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[i];
    int pivot = clause[PIVOT];
    polarity[abs(pivot)] = pivot;

  for (i = S->RATcount - 1; i >= 0; i--) {
    if (S->Skolem[i] == 0) continue;
    int *clause = S->DB + S->Skolem[i];
    int pivot = clause[PIVOT];
    int *newclause = clause;

    if (clause[1] == 0) polarity[abs(pivot)] = pivot;

    while (*clause) {
      if (polarity[abs(*clause)] == *clause && *clause != pivot)
        S->Skolem[i] = 0;
      if (polarity[abs(*clause)] != -(*clause) || *clause == pivot)
        *newclause++ = *clause;
      clause++; }
    *newclause = 0;

    if (S->Skolem[i] == 0) continue;

//    clause = S->DB + S->Skolem[i];
//    if (clause[1] == 0) polarity[abs(pivot)] = pivot;

    if (polarity[abs(pivot)] == pivot) {
      S->DB[S->Skolem[i]  ] = pivot;
      S->DB[S->Skolem[i]+1] = 0; }

    if (polarity[abs(pivot)] == -pivot) {
      polarity[abs(pivot)]  = S->maxVar + 1; }
  }

  for (i = 1; i <= S->maxVar; i++)
    polarity[i] = 0;

  for (i = S->RATcount - 1; i >= 0; i--) {
    if (S->Skolem[i] == 0) continue;
    int *clause = S->DB + S->Skolem[i];
    int pivot = clause[PIVOT];
    if (polarity[abs(pivot)] == pivot) {
      S->Skolem[i] = 0; }

    if (polarity[abs(pivot)] == 0) {
      S->DB[ S->Skolem[i]    ] = pivot;
      S->DB[ S->Skolem[i] + 1] = 0;
      polarity[abs(pivot)] = pivot;
      S->Skolem[S->RATcount++] = S->Skolem[i];
      S->Skolem[i] = 0; }

    if (polarity[abs(pivot)] == -pivot) {
      polarity[abs(pivot)] = S->maxVar + 1; } }

  int j = 0;
  for (i = 0; i < S->RATcount; i++)
    if (S->Skolem[i]) S->Skolem[j++] = S->Skolem[i];

  S->RATcount = j; }

  free (polarity);

  return _RATcount - S->RATcount;
}

void printSkolem (struct solver *S) {
  int i, j;
  int nInputs = 0, nOutputs = 0, nGates = 0;
  int *gate, *last, *polarity, *oGate;

  do {
    while (pureLiteralSubstitution(S)); }
  while (replaceLastByUnit(S));

  gate     = (int*) malloc (sizeof(int) * (S->maxVar + 1));
  oGate    = (int*) malloc (sizeof(int) * (S->maxVar + 1));
  last     = (int*) malloc (sizeof(int) * (S->maxVar + 1));
  polarity = (int*) malloc (sizeof(int) * (S->maxVar + 1));

  for (i = 1; i <= S->maxVar; i++) {
    last    [i] = i;
    polarity[i] = 0; }

  for (i = 1; i <= S->nVars; i++) {
    if (S->level[i] == -1) continue;
    if (S->level[i] % 2) nInputs++;
    else                 nOutputs++; }

  for (i = S->RATcount - 1; i >= 0; i--) {
    int *clause = S->DB + S->Skolem[ i ];
    int pivot = clause[PIVOT];
    int flag   = 0;
    int forced = 1;
    while (*clause) {
      if (polarity[abs(*clause)] != -(*clause)) forced = 0;
      if (polarity[abs(*clause)] ==   *clause ) flag   = polarity[abs(*clause)];
      clause++; }

    if (polarity[abs(pivot)] ==   0  ) polarity[abs(pivot)] = pivot;
    if (polarity[abs(pivot)] != pivot) polarity[abs(pivot)] = S->maxVar + 1; }

  int altRATcount = 0;
  for (i = 1; i <= S->maxVar; i++) {
    if (S->level[i] % 2) continue;
    if (    polarity[i]  == 0) polarity[i] = i;
    if (abs(polarity[i]) == i) altRATcount++; }

  printf("c unit existentials %i ", altRATcount);
  int maxIndex = S->maxVar;

  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[ i ];
    int flag   = 0;
    while (*clause) {
      if (polarity[abs(*clause)] == *clause) flag = 1;
      clause++; }
    if (flag == 0) altRATcount++; }

  printf("out of %i RAT clauses\n", altRATcount);

  nGates = 0;
  int nExtra = 0;
  for (i = S->nVars + 1; i <= S->maxVar; i++)
    if ((S->level[i] % 2) == 0) nExtra++;

  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[ i ];
    int flag =  0;
    while (*clause) {
      if (polarity[abs(*clause)] == *clause) flag = 1;
      clause++; }

    if (flag == 0) {
      int size = 0;
      clause = S->DB + S->Skolem[ i ];
      int pivot = clause[PIVOT];
      int thisLevel = clause[LEVEL];

      if (clause[OUTER]) {
        size++;  // now at least one literal apart from the pivot
        size++;
//        printf("c adding a new variables due to outer clauses\n");
        int *tmp = S->outer + clause[OUTER];
        int dSize = 0;
        while (*tmp) {
          int oSize = 0; dSize++;
          while (*tmp) { oSize++; tmp++; }
          nGates += oSize - 1;
//          printf("c adding %i new variables due to oSize\n", oSize - 1);
          tmp++; }
        if (dSize > 2) //printf("c adding %i new variables due to dSize\n", dSize - 2),
          nGates += dSize - 2; }

      while (*clause) {
        int var = abs(*clause);
        if (polarity[var] != -(*clause) && *clause != pivot && S->level[var] <= thisLevel) size++;
        clause++; }

      if (pivot > 0) nGates++;
      if (size == 0) nGates++;
      else           nGates+= size; } }

// test
//  nGates += nOutputs;

  if (S->aigFile) {
    fprintf(S->aigFile, "aag %i %i 0 %i %i\n", maxIndex + nGates + nExtra, nInputs, nOutputs, nGates + nOutputs + nExtra);
    for (i = 1; i <= S->nVars; i++)
      if ((S->level[i] % 2) == 1) fprintf(S->aigFile, "%i\n", 2 * i);
    for (i = 1; i <= S->nVars; i++) {
      if ( S->level[i]      == -1) continue;
      if ((S->level[i] % 2) ==  0) fprintf(S->aigFile, "%i\n", 2 * i); } }

  int lastVar = S->maxVar + (int) S->nClauses + nGates + 1;
  if (S->skolemFile) {
    int numBinary = 0;

    for (i = 0; i < S->nClauses; i++) {
      int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
      while (*lemmas) numBinary++, lemmas++; }

    fprintf(S->skolemFile, "p cnf %i %i\n", lastVar, nOutputs + nGates * 3 + numBinary + nExtra + 2);

    for (i = 0; i < S->nClauses; i++) fprintf(S->skolemFile, "%i ", S->maxVar + i + 1);
    fprintf(S->skolemFile, "0\n");

    for (i = 0; i < S->nClauses; i++) {
      int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
      while (*lemmas) fprintf(S->skolemFile, "-%i %i 0\n", S->maxVar + i + 1, -(*lemmas++)); } }

  int aux = 2 * (S->maxVar);

//  test
//  for (i = 1; i <= S->nVars; i++)
//    if ((S->level[i] % 2) == 0) {
//      aux += 2;
//      printAND (S, 2 * i, 1, aux, lastVar);
//      last[i] = aux / 2; }

  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[ i ];
    int flag = 0;
    int size = 0;
    int out  = 0;
    while (*clause) {
      if (polarity[abs(*clause)] == *clause) flag = 1;
      clause++; }

    if (flag == 0) {
      clause = S->DB + S->Skolem[ i ];
      if (S->verb) printClause(clause);
      int pivot = clause[PIVOT];
      int thisLevel = clause[LEVEL];

      if (clause[OUTER]) {
        size = 0;
        aux += 2;
        int newaux = aux;
//        printf("c outer clauses: create new aux var  %i\n", aux / 2);
        int *tmp = S->outer + clause[OUTER];
        while (*tmp) {
          int oSize = 0;
          while (*tmp) {
            if (*tmp > 0) oGate[oSize++] =  last[ (*tmp)];
            else          oGate[oSize++] = -last[-(*tmp)];
//            printf("oGate[%i] = %i\n", oSize-1, oGate[oSize-1]);
            tmp++; }
//          printf("oSize = %i\n", oSize);
          if (oSize == 1) {
//            printf("c setting gate[%i] = %i\n", size, -oGate[0]);
            gate[size++] = -oGate[0]; }
          else {
            newaux += 2;
            int output = newaux;
            gate[size++] = newaux / 2;
//            if (oSize == 2) printf("A newaux %i, gate[0] %i, gate[1] %i\n", output, map(oGate[0]), map(oGate[1]));
            if (oSize == 2) printAND(S, output, map(oGate[0]), map(oGate[1]), lastVar);
            else {
              oSize -= 2;
              newaux += 2;
//              printf("B newaux %i, gate[0] %i, gate[1] %i\n", newaux, map(oGate[oSize]), map(oGate[oSize + 1]));
              printAND(S, newaux, map(oGate[oSize]), map(oGate[oSize+1]), lastVar);
              while (oSize > 1) {
                oSize--;
//                printf("C newaux+2 %i, gate[oSize] %i, newaux %i\n", newaux +2, map(oGate[oSize]), newaux);
                printAND(S, newaux + 2, map(oGate[oSize]), newaux, lastVar);
                newaux += 2; }
//              printf("D output %i, gate[0] %i, newaux %i\n", output, map(oGate[0]), newaux);
              printAND(S, output, map(oGate[0]), newaux, lastVar); } } tmp++; }

//        printf("size = %i\n", size);
//        printf("aux %i, 1, gate[0] %i\n", aux, gate[0]);

        if      (size == 1) printAND(S, aux,            1, map(gate[0]), lastVar);
        else if (size == 2) printAND(S, aux, map(gate[0]), map(gate[1]), lastVar);
        else {
          size -= 2;
          newaux += 2;
          printAND(S, newaux, map(gate[size]), map(gate[size+1]), lastVar);
          while (size > 1) {
            size--;
            printAND(S, newaux + 2, map(gate[size]), newaux, lastVar);
            newaux += 2; }
          printAND(S, aux, map(gate[0]), newaux, lastVar); }

//        printf("finished outer clause\n");
        size = 0;
        gate[size++] = -aux / 2;
        aux = newaux; }

      while (*clause) {
        int var = abs(*clause);
        if (polarity[var] != -(*clause) && *clause != pivot && S->level[var] <= thisLevel) {
          if (*clause > 0) gate[size++] =  last[ (*clause)];
          else             gate[size++] = -last[-(*clause)]; }
        clause++; }

      if      (size == 0) out = 1;
      else if (size == 1) out = map(gate[0]);  // binary clause
      else {
        size -= 2;
        aux += 2;
        printAND(S, aux, map(gate[size + 1]), map(gate[size]), lastVar);
        while (size) {
          size--;
          printAND(S, aux + 2, map(gate[size]), aux, lastVar);
          aux += 2; }
        out = aux; }

      if (pivot < 0) {
        printAND (S, last[abs(pivot)] * 2, out ^ 1, aux + 2, lastVar);
        aux += 2; last[abs(pivot)] = aux / 2; }
      else {
        printAND (S, aux + 4, out ^ 1, aux + 3, lastVar);
        printAND (S, last[abs(pivot)] * 2, 1, aux + 5, lastVar);
        aux += 2; last[abs(pivot)] = aux / 2;
        aux += 2; } } }

  if (S->aigFile) {
    for (i = 1; i <= S->maxVar; i++) {
      if (S->level[i] == -1) continue;
      if (S->level[i]  %  2) continue;
      if      (polarity[i] ==  i) fprintf(S->aigFile, "%i %i %i\n", 2 * last[i], 1, 1);
      else if (polarity[i] == -i) fprintf(S->aigFile, "%i %i %i\n", 2 * last[i], 0, 0);
      else                        fprintf(S->aigFile, "%i %i %i\n", 2 * last[i], 1, 1); } }

  if (S->skolemFile) {
    for (i = 1; i <= S->maxVar; i++) {
      if (S->level[i] == -1) continue;
      if (S->level[i]  %  2) continue;
      if (last[i] > S->maxVar) last[i] += (int) S->nClauses;
      if      (polarity[i] ==  i) fprintf(S->skolemFile, " %i 0\n", last[i]);
      else if (polarity[i] == -i) fprintf(S->skolemFile, "-%i 0\n", last[i]);
      else                        fprintf(S->skolemFile, " %i 0\n", last[i]); }
    fprintf(S->skolemFile, "%i 0\n", lastVar); } }

void postprocess (struct solver *S) {
  printCore   (S);
  printProof  (S);
#ifdef BLUEVERSION
  printf("c no-inner %i, inner-passed %i, inner-failed %i, outer-required %i\n", S->inneronly, S->innerpassed, S->innerfailed, S->outerrequired);
  printf("c outer-size %i\n", S->outerSize);

if (S->verb){
  int i;
//  for (i = 0; i < S->outerSize; i++) printf("%i\n", S->outer[i]);
  for (i = 0; i < S->RATcount; i++) {
    int *clause = S->DB + S->Skolem[i];
    if (clause[OUTER] != 0) {
      printClause(clause);
      int *tmp = S->outer + clause[OUTER];
      while (*tmp) {
        while (*tmp) printf("%i ", *tmp++);
        printf("0\n"); tmp++; }
    }
  }
}
#endif
  printSkolem (S);
  printTrace  (S); }

int redundancyCheck (struct solver *S, int *clause, int size, int uni) {
  int i;
  S->REDcount++;
  if (S->verb) { printf("c checking lemma (%i, %i) ", size, clause[PIVOT]); printClause (clause); }
  if ((clause[ID] & ACTIVE) == 0) return SUCCEED;
  if (size < 0) {
    S->DB[ S->reason[abs(*clause)] - 2] |= 1;
    return SUCCEED; }

  S->RATmode = 0;
  if (S->traceFile) {
    fprintf(S->traceFile, "%lu ", S->time >> 1);
    for (i = 0; i < size; ++i) fprintf(S->traceFile, "%i ", clause[i]);
    fprintf(S->traceFile, "0 "); }

  for (i = 0; i < size; ++i) { ASSIGN(-clause[i]); S->reason[abs(clause[i])] = 0; }

  if (propagate (S, 0) == UNSAT) {
    if (S->verb) printf("c lemma has RUP\n");
    return SUCCEED; }

  // Failed RUP check.  Now test RAT.
  // printf("RUP check failed.  Starting RAT check.\n");
  int reslit = clause[PIVOT];
#ifdef QBF
  int thisLevel = S->level[abs(reslit)];
  while (S->levelOcc[ thisLevel+1 ] == 0 && thisLevel < S->maxLevel) {
    thisLevel += 2; }
#endif
  if (S->verb)
    printf("c RUP checked failed; resolution literal %d.\n", reslit);
#ifdef QBF
  if (!uni && thisLevel % 2) {
    printf("c ERROR: trying to perform resolution on universal literal %i\n", reslit);
    return FAILED; } // resolution literal is universally quantified
  if (S->verb)
    printf("c checking redundancy w.r.t. level %i (%i)\n", thisLevel, S->level[abs(reslit)]);
  clause[LEVEL] = thisLevel;
#endif
  int j, blocked, numCandidates;
  long int reason;
  int* savedForced;

#ifdef BLUEVERSION
  int blueflag = 1;
  tryblue:;
#endif
  numCandidates = 0;
  savedForced = S->forced;
  S->RATmode = 1;
  S->currentRATdependencies = 0;
  S->forced = S->assigned;

  // Loop over all literals to calculate resolution candidates
  for (i = -S->maxVar; i <= S->maxVar; i++) {
    if (i == 0) continue;
    // Loop over all watched clauses for literal
    for (j = 0; j < S->used[i]; j++) {
      int* watchedClause = S->DB + (S->wlist[i][j] >> 1);
      if (*watchedClause == i) { // If watched literal is in first position
        int flag = 0;
        blocked = 0;
        reason = 0;
	while (*watchedClause) {
          int lit = *watchedClause++;
#ifdef QBF
          if (S->level[abs(lit)] > thisLevel) continue;
#endif
          if (lit == -reslit) flag = 1;
	  else if (S->false[-lit]) { // Unless some other literal is satisfied
            if (blocked == 0 || reason > S->reason[ abs(lit) ])
              blocked = lit, reason = S->reason[ abs(lit) ]; } }

       if (blocked != 0 && reason != 0 && flag == 1) {
         analyze (S, S->DB + reason, -1); S->reason[abs(blocked)] = 0; }

       // If resolution candidate, add to list
       if (blocked == 0 && flag == 1) {
	 if (numCandidates == S->maxCandidates) {
	   S->maxCandidates = (S->maxCandidates * 3) >> 1;
	   S->resolutionCandidates = realloc(S->resolutionCandidates,
	    		      sizeof(int) * S->maxCandidates); }
	   S->resolutionCandidates[numCandidates++] = S->wlist[i][j] >> 1; } } } }

  // Check all candidates for RUP
  int flag = 1;
  for (i = 0; i < numCandidates; i++) {
    int* candidate = S->DB + S->resolutionCandidates[i];
    if (S->verb) {
      printf("c candidate: "); printClause (candidate); }
    while (*candidate) {
      int lit = *candidate++;
#ifdef QBF
      if (S->level[abs(lit)] > thisLevel) continue;
#endif
      if (lit != -reslit && !S->false[lit]) {
        ASSIGN(-lit); S->reason[abs(lit)] = 0; } }

    if (propagate (S, 0) == SAT) {
      flag  = 0;
#ifdef BLUEVERSION
      if (blueflag == 0) {
        S->outerrequired++;
        candidate = S->DB + S->resolutionCandidates[i];
        while (*candidate) {
          int lit = *candidate++;
          if (S->level[abs(lit)] <= thisLevel && lit != -reslit)
            S->outer[S->outerSize++] = lit; }
        S->outer[S->outerSize++] = 0;
//        printf("c FAILING clause: "); printClause (S->DB + S->resolutionCandidates[i]);
        S->processed = S->forced;
        while (S->forced < S->assigned) S->false[*(--S->assigned)] = 0;
        continue; }
      else
#endif
      break; }
    else if (S->verb) printf("c candidate PASSED blue test (%i)\n", blueflag); }

  S->processed = S->forced = savedForced;
  while (S->forced < S->assigned) S->false[*(--S->assigned)] = 0;

  if (flag) {
    S->Skolem[ S->RATcount ] = (int) (clause - S->DB); }

#ifdef BLUEVERSION
  if (flag) {
    if (blueflag == 0) {
      S->innerpassed++;
      clause[OUTER] = 0; }
    else {
      for (i = 0; i < size; ++i)
        if (S->level[abs(clause[i])] > thisLevel) blueflag = 0;

      if (blueflag == 0) {
        S->processed = S->forced;
        while (S->forced < S->assigned) S->false[*(--S->assigned)] = 0;

        for (i = 0; i < size; ++i)
          if (S->level[abs(clause[i])] <= thisLevel) {
            ASSIGN(-clause[i]); S->reason[abs(clause[i])] = 0; }

        if (propagate (S, 0) == UNSAT) { printf("c ERROR!!!\n"); }
        clause[OUTER] = S->outerSize;
        goto tryblue; }
      else { S->inneronly++; } } }
  else if (blueflag == 0) {
    S->outer[S->outerSize++] = 0;
    S->innerfailed++; flag = 1; }
#endif

  if (flag) { S->RATcount++;
    if (S->verb)
      printf("c lemma has RAT on %i (%i)\n", reslit, S->RATcount - 1);
    if (S->traceFile) {  // This is quadratic, can be n log n
      for (i = 0; i < S->currentRATdependencies; i++) {
	if (S->RATdependencies[i] != 0) {
	  fprintf(S->traceFile, "%d ", S->RATdependencies[i]);
	  for (j = i + 1; j < S->currentRATdependencies; j++)
	    if (S->RATdependencies[j] == S->RATdependencies[i])
	      S->RATdependencies[j] = 0; } }
      fprintf(S->traceFile, "0\n"); }
    return SUCCEED; }

  if (S->verb)
    printf("c RAT check failed\n");
#ifdef QBF
  if (!uni)
#endif
  return FAILED;
#ifdef QBF
  if (S->verb)
    printf("c starting EUR check for level > %i\n", thisLevel);
  return EURcheck (S, clause, reslit);
#endif
}

int verify (struct solver *S) {
  int *delstack;
  if (S->lemmaFile) {
    delstack = (int *) malloc (sizeof(int) * S->count * 2);
    S->delinfo = delstack; }

  if (S->mode == BACKWARD_UNSAT && S->traceFile)
    fprintf(S->traceFile, "%i 0 ", S->count - 1);

  S->time = S->count; // Alternative time init
  if (propagateUnits (S, 1) == UNSAT) {
      printf("c UNSAT via unit propagation on the input instance\n");
      postprocess (S); return UNSAT; }

  int checked;
  int active = S->nClauses;
  for (checked = S->nClauses; checked < S->lastLemma; checked++) {
    long ad = S->adlist[ checked ]; long d = ad & 1;
    int *lemmas = S->DB + (ad >> INFOBITS);

    S->time = lemmas[ID];
    if (d) active--; else active++;
    if (S->mode == FORWARD_SAT && S->verb) printf("c %i active clauses\n", active);

    if (!lemmas[1]) { // found a unit
      int lit = lemmas[0];
      if (S->verb)
        printf("c found unit in proof %i (%li)\n", lit, d);
      if (d) {
        if (S->mode == FORWARD_SAT) {
          removeUnit (S, lit); propagateUnits (S, 0); }
        else {  // no need to remove units while checking UNSAT
          S->adlist[ checked ] = 0; continue; } }
      else {
        if (S->mode == BACKWARD_UNSAT && S->false[-lit]) { S->adlist[checked] = 0; continue; }
        else { addUnit (S, (long) (lemmas - S->DB)); } } }

    if (d && lemmas[1]) { // if delete and not unit
      if ((S->reason[abs(lemmas[0])] - 1) == (lemmas - S->DB)) {
        if (S->mode == BACKWARD_UNSAT) { // ignore pseudo unit clause deletion
          S->adlist[ checked ] = 0; }
        else if (S->mode == FORWARD_SAT) {
          removeWatch(S, lemmas, 0), removeWatch(S, lemmas, 1);
          propagateUnits (S, 0); } }
      else {
        removeWatch(S, lemmas, 0), removeWatch(S, lemmas, 1); }
      if (S->mode == BACKWARD_UNSAT) continue; }

    int size = sortSize (S, lemmas, -2 * d + 1); // after removal of watches

    if (d && S->mode == FORWARD_SAT) {
      if (size == -1) propagateUnits (S, 0);  // necessary?
      if (redundancyCheck (S, lemmas, size, 0) == FAILED) return SAT;
      continue; }

    if (lemmas[1])
      addWatch (S, lemmas, 0), addWatch (S, lemmas, 1);

    if (size == 0) { printf("c conflict claimed, but not detected\n"); return SAT; }  // change to FAILED?
    if (size == 1) {
      if (S->verb)
        printf("c found unit %i\n", lemmas[0]);
      ASSIGN (lemmas[0]); S->reason[abs(lemmas[0])] = ((long) ((lemmas)-S->DB)) + 1;
      if (propagate (S, 1) == UNSAT) goto start_verification;
      S->forced = S->processed; } }

  if (S->mode == FORWARD_SAT && active == 0) {
    postprocess (S); return UNSAT; }
  printf("c ERROR: no conflict\n");
  return SAT;

  start_verification:;
  if (S->lemmaFile) *S->delinfo++ = 0;

  if (S->mode == FORWARD_SAT) {
    printf("c ERROR: found empty clause during SAT check\n"); exit(0); }
  printf("c detected empty clause; start verification via backward checking\n");

  S->forced = S->processed;

  for (; checked >= S->nClauses; checked--) {
    long ad = S->adlist[ checked ]; long d = ad & 1; long uni = 0;
    int *clause = S->DB + (ad >> INFOBITS);

    if (ad == 0) continue; // Skip clause that has been removed from adlist

#ifdef QBF
    uni = ad & UNIVERSAL;
#endif

    if (d == 0) {
      if (clause[1]) {
        removeWatch (S, clause, 0), removeWatch (S, clause, 1);
        if (S->reason[abs(clause[0])] == (clause + 1 - S->DB)) {  // use this check also for units?
          unassignUnit (S, clause[0]); } }
      else unassignUnit (S, clause[0]); }

    int size = sortSize (S, clause, 2 * d - 1); // check the diff

    if (d) {
      if (S->verb) { printf("c adding clause (%i) ", size); printClause(clause); }
      addWatch (S, clause, 0), addWatch (S, clause, 1); continue; }

    S->time = clause[ID];
    if ((S->time & ACTIVE) == 0) continue;  // If not marked, continue

    if (S->verb) {
      printf("c validating clause (%li, %i, %i):  ", uni, clause[PIVOT], size); printClause (clause); }

//    assert (size >=  1);
    assert (size !=  0);
#ifdef QBF
    if (uni && (S->level[abs(clause[PIVOT])] % 2 == 0)) {
      printf ("c ERROR: applying universal reduction on existential literal\n");
      printf ("c in clause "); printClause (clause);
      return SAT;
    }
    if (uni && URcheck (S, checked - 1, clause[PIVOT]) == SUCCEED) continue;
#endif

    struct timeval current_time;
    gettimeofday(&current_time, NULL);
    int seconds = (int) (current_time.tv_sec - S->start_time.tv_sec);
    if (seconds > S->timeout) printf("s TIMEOUT\n"), exit(0);

    if (redundancyCheck (S, clause, size, uni) == FAILED) return SAT;
    if (S->lemmaFile) *(S->delinfo++) = (ad >> INFOBITS) << 1; }

  postprocess (S);
  return UNSAT; }

int compare (const void *a, const void *b) {
  return (*(int*)a - *(int*)b); }

long matchClause (struct solver* S, long *clauselist, int listsize, int* input, int size) {
  int i, j;
  qsort (input, size, sizeof(int), compare);
  for (i = 0; i < listsize; ++i) {
    int *clause = S->DB + clauselist[i];
    for (j = 0; j <= size; j++)
      if (clause[j] != input[j]) goto match_next;

    long result = clauselist[ i ];
    clauselist[ i ] = clauselist[ --listsize ];
    return result;
    match_next:; }
  return 0; }

#ifdef QBF
void parsePrefix (struct solver* S) {
  unsigned int var, tmp, forall = 0;
  for (;;) {
    tmp = fscanf (S->inputFile, " a %i ", &var);
    if (tmp == 1) {
      if (forall == 0) forall = 1, S->maxLevel++; }
    else {
      tmp = fscanf (S->inputFile, " e %i ", &var);
      if (tmp == 1) {
        if (forall == 1) forall = 0, S->maxLevel++; }
      else return; }

    while (var) {
//      printf ("c init level[%i] = %i\n", var, S->maxLevel);
      S->level[ var ] = S->maxLevel;
      var = 0; tmp = fscanf (S->inputFile, " %i ", &var); } } }
#endif

unsigned int getHash (int* input) {
  unsigned int sum = 0, prod = 1, xor = 0;
  while (*input) {
    prod *= *input; sum += *input; xor ^= *input; input++; }
  return (1023 * sum + prod ^ (31 * xor)) % BIGINIT; }

int parse (struct solver* S) {
  int tmp, active = 0;
  int del = 0, uni = 0;
  int *buffer, bsize;

  do { tmp = fscanf (S->inputFile, " cnf %i %li \n", &S->nVars, &S->nClauses);  // Read the first line
    if (tmp > 0 && tmp != EOF) break; tmp = fscanf (S->inputFile, "%*s\n"); }  // In case a commment line was found
  while (tmp != 2 && tmp != EOF);                                              // Skip it and read next line
  int nZeros = S->nClauses;

  bsize = S->nVars * 2;
  if ((buffer = (int*)malloc(bsize * sizeof(int))) == NULL) return ERROR;

  S->count      = 1;
  S->lastLemma  = 0;
  S->mem_used   = 0;                  // The number of integers allocated in the DB

#ifdef BLUEVERSION
  S->inneronly = S->innerpassed = S->innerfailed = S->outerrequired = 0;
#endif

  long size;
  long DBsize = S->mem_used + BIGINIT;
  S->DB = (int*) malloc (DBsize * sizeof(int));
  if (S->DB == NULL) { free (buffer); return ERROR; }

  int i;
#ifdef QBF
  S->level = (int *) malloc ((S->nVars + 1) * sizeof(int )); // Prefix level of variables
  for (i = 1; i <= S->nVars; ++i) S->level[i] = -1;
#endif
  S->maxVar   = S->nVars;
  S->Lcount   = 0;
#ifdef QBF
  S->maxLevel = 0;
  parsePrefix (S);
#endif
  int    admax     = BIGINIT;
         S->adlist = (long* ) malloc (sizeof (long ) * admax);
  long **hashTable = (long**) malloc (sizeof (long*) * BIGINIT);
  int   *hashUsed  = (int * ) malloc (sizeof (int  ) * BIGINIT);
  int   *hashMax   = (int * ) malloc (sizeof (int  ) * BIGINIT);
  for (i = 0; i < BIGINIT; i++) {
    hashUsed [ i ] = 0;
    hashMax  [ i ] = INIT;
    hashTable[ i ] = (long*) malloc (sizeof(long) * hashMax[i]); }

  int fileSwitchFlag = 0;
  size = 0;
  while (1) {
    int lit = 0; tmp = 0;
    fileSwitchFlag = nZeros <= 0;

    if (size == 0) {
#ifdef QBF
      if (!fileSwitchFlag) tmp = fscanf (S->inputFile, " u %i ", &lit);
      else tmp = fscanf (S->proofFile, " u  %i ", &lit);
      if (tmp == EOF && !fileSwitchFlag) fileSwitchFlag = 1;
      uni = tmp > 0;
#endif
      if (!fileSwitchFlag) tmp = fscanf (S->inputFile, " d  %i ", &lit);
      else tmp = fscanf (S->proofFile, " d  %i ", &lit);
      if (tmp == EOF && !fileSwitchFlag) fileSwitchFlag = 1;
      del = tmp > 0; }

    if (!lit) {
      if (!fileSwitchFlag) tmp = fscanf (S->inputFile, " %i ", &lit);  // Read a literal.
      else tmp = fscanf (S->proofFile, " %i ", &lit);
      if (tmp == EOF && !fileSwitchFlag) fileSwitchFlag = 1; }

    if (abs(lit) > S->maxVar) S->maxVar = abs(lit);
    if (S->maxVar >= bsize) { bsize *= 2;
      buffer = (int*) realloc (buffer, sizeof(int) * bsize); }

    if (tmp == EOF && fileSwitchFlag) break;
    if (abs(lit) > S->nVars && !fileSwitchFlag) {
      printf("c illegal literal %i due to max var %i\n", lit, S->nVars); exit(0); }
    if (!lit) {
      if (del && S->mode == BACKWARD_UNSAT && size == 1)  {
        del = 0; uni = 0; size = 0; continue; }
      int rem = buffer[0];
      buffer[ size ] = 0;
//      printf("c "); printClause(buffer);
      unsigned int hash = getHash (buffer);
      if (del || uni) {
        if (S->delete) {
//          int  count = 0;
          long match = 0;
//          for (;;) {
            match = matchClause (S, hashTable[hash], hashUsed[hash], buffer, size);
            if (match == 0) {
//              if (count) break;
              printf("c MATCHING ERROR: "); printClause (buffer); exit (0); }
            if (S->mode == FORWARD_SAT) S->DB[ match - 2 ] = rem;
//            count++;
            hashUsed[hash]--;
            active--;
            if (S->lastLemma == admax) { admax = (admax * 3) >> 1;
              S->adlist = (long*) realloc (S->adlist, sizeof(long) * admax); }
            S->adlist[ S->lastLemma++ ] = (match << INFOBITS) + 1; }
//          if (count > 1) {
//            printf("c WARNING: %i times removed ", count); printClause(buffer); } }
        if (del) { del = 0; uni = 0; size = 0; continue; } }

      if (S->mem_used + size + EXTRA > DBsize) { DBsize = (DBsize * 3) >> 1;
	S->DB = (int *) realloc(S->DB, DBsize * sizeof(int)); }
      int *clause = &S->DB[S->mem_used + EXTRA - 1];
      if (size != 0) clause[PIVOT] = buffer[0];
      clause[ID] = 2 * S->count; S->count++;
      clause[OUTER] = 0;
      if (S->mode == FORWARD_SAT) if (nZeros > 0) clause[ID] |= ACTIVE;
#ifdef QBF
      if (uni) {
        clause[PIVOT] = rem;
        int x; for (x = 0; x < size; x++)
          if (buffer[x] == rem)
            buffer[x] = buffer[--size], buffer[size] = 0; }
#endif
//      printf("c "); printClause(buffer);

      qsort (buffer, size, sizeof(int), compare);
      for (i = 0; i < size; ++i) { clause[ i ] = buffer[ i ]; } clause[ i ] = 0;
      S->mem_used += size + EXTRA;

      hash = getHash (clause);
      if (hashUsed[hash] == hashMax[hash]) { hashMax[hash] = (hashMax[hash] * 3) >> 1;
        hashTable[hash] = (long *) realloc(hashTable[hash], sizeof(long*) * hashMax[hash]); }
      hashTable[ hash ][ hashUsed[hash]++ ] = (long) (clause - S->DB);

      active++;
      if (S->lastLemma == admax) { admax = (admax * 3) >> 1;
        S->adlist = (long*) realloc (S->adlist, sizeof(long) * admax); }
      S->adlist[ S->lastLemma++ ] = (((long) (clause - S->DB)) << INFOBITS) + 2 * uni;
      if (nZeros <= 0) S->Lcount++;

      if (!nZeros) S->lemmas   = (long) (clause - S->DB);    // S->lemmas is no longer pointer
      size = 0; del = 0; uni = 0; --nZeros; }                // Reset buffer
   else buffer[ size++ ] = lit; }                            // Add literal to buffer

  if (S->mode == FORWARD_SAT && active) {
    printf("c WARNING: %i clauses active if proof succeeds\n", active);
    for (i = 0; i < BIGINIT; i++) {
      int j;
      for (j = 0; j < hashUsed[i]; j++) {
        printf("c ");
        int *clause = S->DB + hashTable [i][j];
        printClause (clause);
        if (S->lastLemma == admax) { admax = (admax * 3) >> 1;
            S->adlist = (long*) realloc (S->adlist, sizeof(long) * admax); }
        S->adlist[ S->lastLemma++ ] = (((int)(clause - S->DB)) << INFOBITS) + 1; } } }

  S->DB = (int *) realloc(S->DB, S->mem_used * sizeof(int));

  for (i = 0; i < BIGINIT; i++) free (hashTable[i]);
  free (hashTable);
  free (hashUsed);
  free (hashMax);
  free (buffer);

  printf ("c finished parsing\n");

  int n = S->maxVar;
  S->falseStack = (int*) malloc((n + 1) * sizeof(int)); // Stack of falsified literals -- this pointer is never changed
  S->forced     = S->falseStack;      // Points inside *falseStack at first decision (unforced literal)
  S->processed  = S->falseStack;      // Points inside *falseStack at first unprocessed literal
  S->assigned   = S->falseStack;      // Points inside *falseStack at last unprocessed literal
  S->Skolem     = (int *) malloc((S->nClauses + S->lastLemma) * sizeof(int));
  S->reason     = (long*) malloc((    n + 1) * sizeof(long)); // Array of clauses
  S->used       = (int *) malloc((2 * n + 1) * sizeof(int )); S->used  += n; // Labels for variables, non-zero means false
  S->max        = (int *) malloc((2 * n + 1) * sizeof(int )); S->max   += n; // Labels for variables, non-zero means false
  S->false      = (int *) malloc((2 * n + 1) * sizeof(int )); S->false += n; // Labels for variables, non-zero means false
#ifdef QBF
  S->rep        = (int *) malloc((    n + 1) * sizeof(int )); // Representative of variables
  S->levelOcc   = (int *) malloc((    n + 1) * sizeof(int )); // Variable occurrence per level
#endif

  S->arcs     = 0;
  S->RATmode  = 0;
  S->RATcount = 0;
  S->REDcount = 0;
#ifdef BLUEVERSION
  S->outerAlloc    = OUTER_INIT_SIZE;
  S->outer = (int*) malloc (sizeof(int) * S->outerAlloc);
  S->outer[0]  = 0;
  S->outer[1]  = 0;
  S->outerSize = 2;
#endif
  S->maxCandidates = CANDIDATE_INIT_SIZE;
  S->resolutionCandidates = (int*) malloc(sizeof(int) * S->maxCandidates);
  for (i = 0; i < S->maxCandidates; i++) S->resolutionCandidates[i] = 0;

  S->maxRATdependencies = RAT_DEPENDENCIES_INIT_SIZE;
  S->RATdependencies = (int*) malloc(sizeof(int) * S->maxRATdependencies);
  for (i = 0; i < S->maxRATdependencies; i++) S->RATdependencies[i] = 0;

  for (i = 1; i <= n; ++i) { S->reason    [i]           =    0;
                             S->falseStack[i]           =    0;
#ifdef QBF
                             S->levelOcc  [i]           =    0;
#endif
	                     S->false[i] = S->false[-i] =    0;
                             S->used [i] = S->used [-i] =    0;
                             S->max  [i] = S->max  [-i] = INIT; }

  S->wlist = (long**) malloc (sizeof(long*) * (2*n+1)); S->wlist += n;

  for (i = 1; i <= n; ++i) { S->wlist[ i] = (long*) malloc (sizeof(long) * S->max[ i]); S->wlist[ i][0] = END;
                             S->wlist[-i] = (long*) malloc (sizeof(long) * S->max[-i]); S->wlist[-i][0] = END; }

  S->unitSize  = 0;
  S->unitStack = (long *) malloc (sizeof(long) * n);

  for (i = 0; i < S->nClauses; i++) {
    int *clause = S->DB + (S->adlist[i] >> INFOBITS);
    if (clause[1]) { addWatch (S, clause, 0); addWatch (S, clause, 1); }
    else if (S->false[ clause[0] ]) {
      printf ("c found complementary unit clauses\n");
      if (S->coreFile) {
        fprintf (S->coreFile, "p cnf %i 2\n%i 0\n%i 0\n", abs(clause[0]), clause[0], -clause[0]);
        fclose (S->coreFile); }
      if (S->lemmaFile) {
        fprintf (S->lemmaFile, "0\n");
        fclose (S->lemmaFile); }
      return UNSAT; }
    else {
//    else if (!S->false[ -clause[0] ]) {
//      ASSIGN (clause[0]);
      S->false[-(clause[0])] = 1;
      addUnit (S, (long) (clause - S->DB)); }
#ifdef QBF
    while (*clause) {  // only required for QBF
      int var = abs(*clause++);
      if (S->level[var] == -1) S->level[var] = 0;
      S->levelOcc[ S->level[var] ]++; }
#endif
  }
//  for (i = -S->nVars; i <= S->nVars; i++) S->false[i] = 0;

#ifdef QBF
  int *maxseen;  maxseen  = (int *) malloc (sizeof (int) * (S->maxVar + 1));
  int *polarity; polarity = (int *) malloc (sizeof (int) * (S->maxVar + 1));
  S->level = (int*) realloc (S->level, sizeof(int) * (S->maxVar + 1));
//  for (i = S->nVars + 1; i <= S->maxVar; i++) {
//    printf ("c fixing level[%i] = %i\n", i, S->maxLevel);
//    S->level[i] = S->maxLevel;
//  }
  for (i = S->nVars + 1; i <= S->maxVar; i++) {
    S->level[i] = -1;
    maxseen[i] = polarity[i] = 0; }

  for (i = S->nClauses; i < S->lastLemma; i++) {
    long ad = S->adlist[ i ]; long d = ad & 1;
    int *lemmas = S->DB + (ad >> INFOBITS);
    int max = 0;
    while (*lemmas) {
      if (S->level[abs(*lemmas)] > max) max = S->level[abs(*lemmas)];
      lemmas++; }
    lemmas = S->DB + (ad >> INFOBITS);
    max = max + (max % 2);
    while (*lemmas) {
      int lit = *lemmas++; int var = abs(lit);
      if (S->level[var] == -1) {
        if (polarity[var] != -lit) {
          polarity[var] = lit;
          if (max > maxseen[var]) {
//            printf ("c setting temp level[%i] to %i\n", var, max);
            maxseen[var] = max;
          }
        }
        else {
//          printf ("c fixing level[%i] = %i\n", var, maxseen[var]);
          S->level[var] = maxseen[var];
        }
      }
    }
  }

  free (maxseen);
  free (polarity);

  for (i = 1; i <= n; i++) if (S->level[i] == -1) S->level[i] = S->maxLevel;
#endif
  return SAT; }

void freeMemory(struct solver *S) {
  if (S->verb) printf("c free memory with maxVar = %i\n", S->maxVar);
  free (S->DB);
  free (S->falseStack);
  free (S->reason);
  free (S->adlist);
  int i; for (i = 1; i <= S->maxVar; ++i) { free (S->wlist[i]); free (S->wlist[-i]); }
  free (S->used  - S->maxVar);
  free (S->max   - S->maxVar);
  free (S->false - S->maxVar);
  free (S->wlist - S->maxVar);
  free (S->resolutionCandidates);
  free (S->RATdependencies);
  return; }

void printHelp ( ) {
  printf("usage: qrat-trim [INPUT] [<PROOF>] [<option> ...]\n\n");
  printf("where <option> is one of the following\n\n");
  printf("  -h          print this command line option summary\n");
  printf("  -c CORE     prints the unsatisfiable core to the file CORE\n");
  printf("  -a AIG      prints the Skolem functions to the file AIG\n");
  printf("  -s CNF      prints the Skolem check file\n");
  printf("  -l LEMMAS   prints the core lemmas to the file LEMMAS\n");
  printf("  -r TRACE    resolution graph in TRACECHECK format\n\n");
  printf("  -t <lim>    time limit in seconds (default %i)\n", TIMEOUT);
  printf("  -u          default unit propatation (i.e., no core-first)\n");
  printf("  -v          more verbose output\n");
  printf("  -p          run in plain mode (i.e., ignore deletion information)\n\n");
  printf("  -S          run in SAT check mode (forward checking)\n\n");
  printf("and input and proof are specified as follows\n\n");
  printf("  INPUT       input file in DIMACS format\n");
  printf("  PROOF       proof file in QRAT format (stdin if no argument)\n\n");
  exit(0); }

int main (int argc, char** argv) {
  struct solver S;

  S.inputFile  = NULL;
  S.proofFile  = stdin;
  S.coreFile   = NULL;
  S.aigFile    = NULL;
  S.skolemFile = NULL;
  S.lemmaFile  = NULL;
  S.traceFile  = NULL;
  S.timeout    = TIMEOUT;
  S.mask       = 0;
  S.verb       = 0;
  S.mode       = BACKWARD_UNSAT;
  S.delete     = 1;
  gettimeofday(&S.start_time, NULL);

  int i, tmp = 0;
  for (i = 1; i < argc; i++) {
    if        (argv[i][0] == '-') {
      if      (argv[i][1] == 'h') printHelp ();
      else if (argv[i][1] == 'a') S.aigFile    = fopen (argv[++i], "w");
      else if (argv[i][1] == 'c') S.coreFile   = fopen (argv[++i], "w");
      else if (argv[i][1] == 'l') S.lemmaFile  = fopen (argv[++i], "w");
      else if (argv[i][1] == 's') S.skolemFile = fopen (argv[++i], "w");
      else if (argv[i][1] == 'r') S.traceFile  = fopen (argv[++i], "w");
      else if (argv[i][1] == 't') S.timeout    = atoi(argv[++i]);
      else if (argv[i][1] == 'u') S.mask       = 1;
      else if (argv[i][1] == 'v') S.verb       = 1;
      else if (argv[i][1] == 'p') S.delete     = 0;
      else if (argv[i][1] == 'S') S.mode       = FORWARD_SAT; }
    else {
      tmp++;
      if (tmp == 1) {
        S.inputFile = fopen (argv[1], "r");
        if (S.inputFile == NULL) {
          printf("c error opening \"%s\".\n", argv[i]); return ERROR; } }

      else if (tmp == 2) {
        S.proofFile = fopen (argv[2], "r");
        if (S.proofFile == NULL) {
          printf("c error opening \"%s\".\n", argv[i]); return ERROR; } } } }

  if (tmp == 1) printf ("c reading proof from stdin\n");
  if (tmp == 0) printHelp ();

  int parseReturnValue = parse(&S);

  fclose (S.inputFile);
  fclose (S.proofFile);
  int sts = ERROR;
  if       (parseReturnValue == ERROR)    printf ("s MEMORY ALLOCATION ERROR\n");
  else if  (parseReturnValue == UNSAT)    printf ("c trivial UNSAT\ns VERIFIED\n");
  else if  ((sts = verify (&S)) == UNSAT) printf ("s VERIFIED\n");
  else printf ("s NOT VERIFIED\n")  ;
  freeMemory (&S);
  return (sts != UNSAT); // 0 on success, 1 on any failure
}
