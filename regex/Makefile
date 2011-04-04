# input files
_CATS=
_SATS= regexp charset dfa linset charset_vt
_DATS= test regexp charset dfa linset charset_vt
_LIBS=

# compilers and flags
CC= gcc
debug : CFLAGS= -D_ATS_GCATS
release : CFLAGS= -O3 -msse -D_ATS_GCATS
LDFLAGS= $(patsubst %,-l%,$(_LIBS))
typecheck: ATSFLAGS= -tc
debug: ATSFLAGS= -g
release: ATSFLAGS=
#ATSCC=$(ATSHOME)/bin/atscc
ATSCC=atscc
debug: ODIR=debug
release: ODIR=release

# ###### ###### #

CFILES= $(patsubst %,%_dats.c,$(_DATS)) $(patsubst %,%_sats.c,$(_SATS))
SATSFILES=$(patsubst %,SATS/%.sats,$(_SATS))
DATSFILES=$(patsubst %,DATS/%.dats,$(_DATS))

####

# silly (should have used automake for configuration),
# but works
debug: test
release: test
typecheck: test

####

test:
	$(ATSCC) $(ATSFLAGS) -o test $(DATSFILES) $(SATSFILES) $(CFLAGS) $(LDFLAGS)

####

clean::
	rm -f $(CFILES)

cleanall: clean
	rm -f test

####

.PHONY: test

##### end of Makefile ####
