CC=gcc
CFLAGS=-g -O2

install: qrat-trim

qrat-trim: qrat-trim.c
	$(CC) qrat-trim.c $(CFLAGS) -o qrat-trim

clean:
	rm -f *~
	rm -rf *.dSYM

superclean: clean
	rm -f qrat-trim

