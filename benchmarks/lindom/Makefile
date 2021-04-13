#!/bin/bash
SHELL = /bin/bash

run:
	(pushd qproof; make run INTERP=$(INTERP))
	(pushd qrat; make run INTERP=$(INTERP))

data:
	(pushd qproof; make data)
	(pushd qrat; make data)

clean:
	rm -f *.pyc *~

superclean: clean
	(pushd qproof; make superclean)
	(pushd qrat; make superclean)

