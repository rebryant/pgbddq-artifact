This archive provides a demonstration version of a proof-generating
QBF solver based on BDDs.  The solver generates proofs in two formats:
* QPROOF: Formulated particularly for this solver
* QRAT:   As documented in https://www.cs.utexas.edu/~marijn/skolem/

A checker for both formats is included.

The program also generates and tests a benchmark based on the Linear
Domino Placement game.

1. System Requirements

       * Python interpreter.  By default, the program runs python3.
         You can change by editing the "INTERP" definition in the
         top-level Makefile

       * C compiler.  The QRAT checker is written in C.  Just about
         any compiler should work.  The default is gcc.

2. Installation and Running Demonstration

All code and benchmark data can be downloaded via Github:

   git clone https://github.com/rebryant/pgbddq-artifact

Once downloaded, the two demonstrations can be run with the command
"make".  The solver will be run twice: once to generate and check
proofs in QPROOF format, and the other to generate and check proofs in
QRAT format.

Both runs test a selection of cases that generate true and false
formulas, and with three proof types: dual, satisfaction, and
refutation.  When running, a lot of stuff gets printed, but there
should be no error messages.  Two tables of generated data get printed
at the end.

3. Makefile options:

all: (Default)
  Combines install, run, data

install:
  Compiles the QRAT checker.  No other installation steps are required.

run:
  Runs the solver on the benchmarks twice---once to generate QPROOF proofs,
  and one to generate QRAT proofs.

data:
   Generates tables showing the results.  These document the clauses
   (both the number of clauses in the input file and the total number
   of clauses generated as part of the proof.  They also show the
   elapsed time in seconds for the solver and the checker.

clean:
  Delete all generated files, except for any benchmark data

superclean:
  Delete all generated files, including the benchmark data

