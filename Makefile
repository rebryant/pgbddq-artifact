# Set to the version of Python installed on this machine
INTERP=python3

all: run data

install:
	(cd qrat-trim ; make install)

run: install
	(cd benchmarks; make run INTERP=$(INTERP))

data:
	(cd benchmarks; make data)

clean:
	rm -rf *~ *.pyc

superclean: clean
	(cd benchmarks ; make superclean)
	(cd qrat-trim ; make superclean)
	(cd solver ; make superclean)



