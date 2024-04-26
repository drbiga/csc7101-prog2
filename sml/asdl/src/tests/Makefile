# Makefile for ASDL tests
#
# COPYRIGHT (c) 2018 The Fellowship of SML/NJ (http://www.smlnj.org)
# All rights reserved.
#
# src/tests/Makefile.  Generated from Makefile.in by configure.
#

SHELL =			/bin/bash


BUILD_DIRS =		basics primitives

.PHONY:		build local-install install

local-install:	build

install:	build

build:
	for dir in $(BUILD_DIRS); do \
	  (cd $$dir && $(MAKE) build) || exit $$?; \
	done

#################### Cleanup ####################

CLEAN_SUBDIRS =		$(BUILD_DIRS)

DISTCLEAN_FILES +=      Makefile

DEVCLEAN_FILES =

include /home/biga/lsu/classes/csc7101/prog2/sml/asdl/mk/clean-rules.gmk
