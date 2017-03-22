# makefile for the lambda-calculus interpreter
SATSFILES = shared/disj.sats shared/types.sats shared/tas.sats \
  frontend/absyn.sats frontend/parse.sats frontend/trans.sats \
  backend/eval.sats
DATSFILES = shared/tas.dats \
  frontend/absyn.dats frontend/parse.dats frontend/trans.dats \
  backend/eval.dats
OFILES = $(patsubst %.dats,%_dats.o,$(DATSFILES)) $(patsubst %.sats,%_sats.o,$(SATSFILES))
CFILES = $(patsubst %.dats,%_dats.c,$(DATSFILES)) $(patsubst %.sats,%_sats.c,$(SATSFILES))

CC = gcc
CFLAGS = -Wall

ATSFLAGS = -g -D_ATS_GCATS

stlc: $(OFILES) main_dats.o
	atscc $(ATSFLAGS) $(OFILES) main_dats.o -o $@ parcomb/libparcomb.a

%_dats.o: %.dats
	atscc $(ATSFLAGS) -IATSparcomb -o $@ -c $<

%_sats.o: %.sats
	atscc $(ATSFLAGS) -IATSparcomb -o $@ -c $<

clean:
	rm -f $(OFILES) $(CFILES) main_dats.c main_dats.o stlc
