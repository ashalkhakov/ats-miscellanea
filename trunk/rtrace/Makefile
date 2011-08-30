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

## - types of builds (what we want as a result?)
##  - typecheck current module (don't compile)
##  - make a debug, profiling or release build
##   - indicated by a target
##  - automake: too heavy (not much time for this)
## - wishlist
##  - put binaries into the bin subdirectory
##  - put temporary files into a subdirectory
##    - atscc strips subdirectories from input file names
##    - don't know the magic to call atsopt+gcc myself
##    - need different directories for different builds!
##  - correctly clean up after building
##
## for now, we do a full rebuild each time,
## this is recommended in the GCC documentation as to help
## the compiler to produce more efficient binaries.
## also, I'm lazy and rtrace is not so big.

# input files
_CATS=
_SATS= vec geom scene accs imbuf
_DATS= rtrace-simp vec geom scene accs_bvh imbuf
_LIBS= m

# compilers and flags
CC= gcc
debug : CFLAGS= -Wall
release : CFLAGS= -O3 -msse
LDFLAGS= $(patsubst %,-l%,$(_LIBS))
typecheck: ATSFLAGS= -tc
debug: ATSFLAGS= -g
release: ATSFLAGS=
ATSCC= $(ATSHOME)/bin/atscc
debug: ODIR=debug
release: ODIR=release

# ###### ###### #

CFILES= $(patsubst %,%_dats.c,$(_DATS)) $(patsubst %,%_sats.c,$(_SATS))
SATSFILES=$(patsubst %,SATS/%.sats,$(_SATS))
DATSFILES=$(patsubst %,DATS/%.dats,$(_DATS))

####

# silly (should have used automake for configuration),
# but works
debug: rtrace
release: rtrace
typecheck: rtrace

####

rtrace:
	$(ATSCC) $(ATSFLAGS) -o rtrace $(DATSFILES) $(SATSFILES) $(CFLAGS) $(LDFLAGS)

####

clean::
	rm -f $(CFILES)

cleanall: clean
	rm -f rtrace

####

.PHONY: rtrace

##### end of Makefile ####
