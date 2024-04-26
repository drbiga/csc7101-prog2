# Makefile for testing primitive pickling operations
#
# COPYRIGHT (c) 2018 The Fellowship of SML/NJ (http://www.smlnj.org)
# All rights reserved.
#
# src/tests/primitives/Makefile.  Generated from Makefile.in by configure.
#

SHELL =			/bin/bash


ASDL_LIBDIR =		/home/biga/lsu/classes/csc7101/prog2/sml/asdl/lib

CXX =			g++
CXXFLAGS =		-g -O2
CPPFLAGS =		 -I/opt/local/include -I/home/biga/lsu/classes/csc7101/prog2/sml/asdl/include
LDFLAGS =		 -L/opt/local/lib -L$(ASDL_LIBDIR)
LIBS =			-lgmp -lasdl

CXX_SRCS =          	cxx-test.cxx
CXX_OBJS =          	$(patsubst %.cxx,%.o,$(CXX_SRCS))

build:		cxx-test sml-test

##### C++ test
#
cxx-test:	$(CXX_OBJS)
	$(CXX) -o $@ $(CXX_OBJS) $(LDFLAGS) $(LIBS)

%.o : %.cxx
	$(CXX) -c $(CPPFLAGS) $(CXXFLAGS) $<

##### SML test
#
sml-test:

.PHONY:		build

build:

#################### Cleanup ####################

CLEAN_FILES =		cxx-test \
			$(CXX_OBJS)

DISTCLEAN_FILES +=      Makefile

DEVCLEAN_FILES =

include /home/biga/lsu/classes/csc7101/prog2/sml/asdl/mk/clean-rules.gmk
