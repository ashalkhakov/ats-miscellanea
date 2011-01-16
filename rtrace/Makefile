#
# Author: Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
# Time: December 23, 2010
#

CATSFILES=
SATSFILES= SATS/vec.sats SATS/geom.sats SATS/scene.sats SATS/bvh.sats SATS/imbuf.sats
DATSFILES= DATS/rtrace-simp.dats DATS/vec.dats DATS/geom.dats DATS/scene.dats DATS/bvh.dats DATS/imbuf.dats
OFILES= $(patsubst %.dats,%_dats.o,$(DATSFILES)) $(patsubst %.sats,%_sats.o,$(SATSFILES))
CFILES= $(patsubst %.dats,%_dats.o,$(DATSFILES)) $(patsubst %.sats,%_sats.c,$(SATSFILES))

CC= gcc
CFLAGS= -Wall
ATSFLAGS= -g
ATSCC=atscc

####

all: rtrace clean

####

rtrace: $(OFILES)
	$(ATSCC) -o rtrace $(OFILES) -lm

%_dats.o: %.dats
	$(ATSCC) $(ATSFLAGS) -o $@ -c $<

%_sats.o: %.sats
	$(ATSCC) $(ATSFLAGS) -o $@ -c $<

####

clean::
	rm -f $(OFILES) $(CFILES)

cleanall: clean
	rm -f rtrace

##### end of Makefile ####
