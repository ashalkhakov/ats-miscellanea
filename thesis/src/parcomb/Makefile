######
#
# Makefile for the [parcomb] package
#
######

checkall:: compall cleanall

compall:: \
  calc1 calc2 calc3 lambda

libparcomb.a: posloc_sats.o posloc_dats.o parcomb_sats.o parcomb_dats.o tokenize_sats.o tokenize_dats.o
	ar r $@ posloc_sats.o posloc_dats.o parcomb_sats.o parcomb_dats.o tokenize_sats.o tokenize_dats.o
	ranlib $@

######

calc1: calc1_example.dats libparcomb.a
	atscc -D_ATS_GCATS -o calc1 \
           calc1_example.dats libparcomb.a

######

calc2: calc2_example.dats libparcomb.a
	atscc -D_ATS_GCATS -o calc2 calc2_example.dats \
          libparcomb.a

######

calc3: calc3_example.dats libparcomb.a
	atscc -D_ATS_GCATS -o calc3 calc3_example.dats \
           libparcomb.a

######

lambda: lambda_example.dats libparcomb.a
	atscc -D_ATS_GCATS -o lambda lambda_example.dats \
           libparcomb.a

######

posloc_dats.o: posloc.dats
	atscc -c -o posloc_dats.o posloc.dats

posloc_sats.o: posloc.sats
	atscc -c -o posloc_sats.o posloc.sats

parcomb_sats.o: parcomb.sats
	atscc -c -o parcomb_sats.o parcomb.sats

parcomb_dats.o: parcomb.dats
	atscc -c -o parcomb_dats.o parcomb.dats

tokenize_dats.o: tokenize.dats
	atscc -c -o tokenize_dats.o tokenize.dats

tokenize_sats.o: tokenize.sats
	atscc -c -o tokenize_sats.o tokenize.sats

######

clean::
	rm -f *~ a.out *_?ats.c *_?ats.o

cleanall: clean
	rm -f calc1 calc2 calc3 lambda

###### end of [Makefile] ######
