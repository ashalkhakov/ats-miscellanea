##
## rtrace -- a typeful ray tracer program
##
## Copyright (C) 2011 Artyom Shalkhakov
##
## All rights reserved
##
## rtrace is free software;  you can  redistribute it and/or modify it
## under the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published
## by the Free Software Foundation; either version 2.1, or (at your option)
## any later version.
## 
## rtrace is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY
## or FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  rtrace;  see the  file COPYING.  If not, please write to
## the Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston,
## MA 02110-1301, USA.

##
## Author: Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
## Time: December 23, 2010
##

CATSFILES=
SATSFILES= SATS/vec.sats SATS/geom.sats SATS/scene.sats SATS/accs.sats SATS/imbuf.sats
DATSFILES= DATS/rtrace-simp.dats DATS/vec.dats DATS/geom.dats DATS/scene.dats DATS/accs_bvh.dats DATS/imbuf.dats
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
