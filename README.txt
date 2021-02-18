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

4. Interpreting the Results

The following shows the printout generated for the benchmark.  These
were measured on a 3.0 GHz Intel Core i7-9700 CPU running Linux.

The column headings are:

  Proof: Proof type.  Either DUAL, SAT (satsifaction), or REF
         (refutation).

  Result: Was the formula true or false

  N: Size of board

  I Cls: Input clauses

  T Cls: Total clauses

  Solve: Elapsed time (in seconds) used by the solver.

  Qproof: Elapsed time (in seconds) used by the checker qchecker.py.

  Qrat: Elapsed time (in seconds) used by the checker qrat-trim.

Here are the results with the solver generating QPROOF proof files:
****************************************************************
Proof	Result	N	I Cls	T Cls	Solve	Qproof	Qrat
DUAL	TRUE	05	82	6710	0.15	0.15	
DUAL	TRUE	10	666	132138	2.99	3.06	
DUAL	TRUE	15	1725	628392	14.69	14.91	
DUAL	FALSE	05	81	6052	0.15	0.13	
DUAL	FALSE	10	664	132403	3.01	3.00	
DUAL	FALSE	15	1728	629530	14.61	15.05	
SAT	TRUE	05	82	5238	0.10	0.07	
SAT	TRUE	10	666	90924	1.76	1.29	
SAT	TRUE	15	1725	406161	8.16	5.94	
REF	FALSE	05	81	5937	0.11	0.08	
REF	FALSE	10	664	126127	2.38	1.81	
REF	FALSE	15	1728	381593	7.60	5.49	
****************************************************************

Here are the results with the solver generating QRAT proof files:
****************************************************************
Proof	Result	N	I Cls	T Cls	Solve	Qproof	Qrat
DUAL	TRUE	05	82	9730	0.16		0.114
DUAL	TRUE	10	666	190377	3.26		2.819
DUAL	TRUE	15	1725	903105	16.60		36.282
DUAL	FALSE	05	81	8806	0.15		0.114
DUAL	FALSE	10	664	190856	3.26		6.226
DUAL	FALSE	15	1728	904596	16.61		93.391
SAT	TRUE	05	82	8520	0.11		0.114
SAT	TRUE	10	666	145576	2.05		2.268
SAT	TRUE	15	1725	648942	9.77		27.866
REF	FALSE	05	81	9877	0.12		0.215
REF	FALSE	10	664	210605	2.83		15.844
REF	FALSE	15	1728	628361	8.94		88.232
****************************************************************

5. To get more information.
 
Log files for the individual runs are in files named
benchmarks/lindom/{qproof,qrat}/*.data.

The file names are a bit cryptic, but they are designed to provide the
entries to the tables when listed in sorted order.  For example, the
first file in the qproof directory is named:
"lindom-3A-DUAL-TRUE-05-bd.data" with the parts of the name indicating:

  lindom: Linear Domino benchmark
  3A:     Forms the first part of Table 3 in the paper.
  DUAL:   Dual proof type
  TRUE:   The formula is true
  05:     N=5
  bd:     Formula generated for B as the player, with a dual proof


