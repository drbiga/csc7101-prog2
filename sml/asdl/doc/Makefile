# Makefile for ASDL documentation
#
# This code is part of the SML/NJ system (http://smlnj.org)
#
# COPYRIGHT (c) 2016 The Fellowship of SML/NJ
# All rights reserved.
#
# doc/Makefile.  Generated from Makefile.in by configure.
#

SHELL =		/bin/sh
PREFIX =	/home/biga/lsu/classes/csc7101/prog2/sml

DIRS =		manual-3.0

.PHONY:		pdf local-install install

pdf:
	for dir in $(DIRS) ; do \
	    (cd $$dir; make pdf) \
	done

local-install:

install:

#################### Cleanup ####################

CLEAN_SUBDIRS =		$(DIRS)

DISTCLEAN_FILES +=      Makefile

DEVCLEAN_FILES =

include /home/biga/lsu/classes/csc7101/prog2/sml/asdl/mk/clean-rules.gmk
