#!/bin/bash
SHELL = /bin/bash

run:
	(pushd lindom; make run INTERP=$(INTERP))

data:
	(pushd lindom; make data)

clean:
	rm -f *.pyc *~

superclean: clean
	(pushd lindom; make superclean)

