# Makefile for the ASDL manual (Version 3.0)
#
# This code is part of the SML/NJ system (http://smlnj.org)
#
# COPYRIGHT (c) 2018 The Fellowship of SML/NJ
# All rights reserved.
#
# doc/manual-3.0/Makefile.  Generated from Makefile.in by configure.
#

SHELL =			/bin/sh
PREFIX =		/home/biga/lsu/classes/csc7101/prog2/sml

.PHONY:		pdf clean distclean devclean

pdf:		manual.pdf

manual.pdf:	$(wildcard *.tex) $(wildcard code/*.asdl)
	latexmk -pdf manual

.PHONY:		clean distclean devclean

clean:
	latexmk -C manual

distclean:	clean
	rm -f Makefile.in

devclean:	distclean
