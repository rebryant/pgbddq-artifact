This directory is used for running benchmarks.
Currently, the only benchmark is the Linear Domino Placement game.

FILES:

Makefile
   Run "make run" to have it solve a set of benchmark files
   Run "make data" to have it tabulate the results
   Run "make clean" to delete unimportant files
   Run "make superclean" to have it delete the benchmark results

serialize.py
   Utility used to serialize quantifier blocks.  Used when
   generating benchmarks for the qrat-trim checker

wrap.py
   Utility used to wrap existing program so that can set timeout limit
   and also measure the elapsed time




