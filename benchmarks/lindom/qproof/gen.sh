#!/bin/bash

echo "Test Dual Proofs for True Cases"
make bd CAT='-3A-DUAL-TRUE' N=05
make ad CAT='-3A-DUAL-TRUE' N=10
make bd CAT='-3A-DUAL-TRUE' N=15

echo "Test Dual Proofs for False Cases"
make ad CAT='-3B-DUAL-FALSE' N=05
make bd CAT='-3B-DUAL-FALSE' N=10
make ad CAT='-3B-DUAL-FALSE' N=15

echo "Test Satisfaction Proofs for True Cases"
make bs CAT='-4A-SAT-TRUE' N=05
make as CAT='-4A-SAT-TRUE' N=10
make bs CAT='-4A-SAT-TRUE' N=15

echo "Test Refutation Proofs for False Cases"
make ar CAT='-4B-REF-FALSE' N=05
make br CAT='-4B-REF-FALSE' N=10
make ar CAT='-4B-REF-FALSE' N=15
