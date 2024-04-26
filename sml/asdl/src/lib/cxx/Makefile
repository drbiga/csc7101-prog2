# Makefile for C++ ASDL library
#
# COPYRIGHT (c) 2018 The Fellowship of SML/NJ (http://www.smlnj.org)
# All rights reserved.
#
# src/lib/cxx/Makefile.  Generated from Makefile.in by configure.
#

SHELL =			/bin/bash


#
# paths to local installation directories
#
ASDL_LIBDIR =		/home/biga/lsu/classes/csc7101/prog2/sml/asdl/lib
ASDL_INCDIR =		/home/biga/lsu/classes/csc7101/prog2/sml/asdl/include/asdl

#
# paths to installation directories
#
PREFIX =		/home/biga/lsu/classes/csc7101/prog2/sml
INSTALL_LIBDIR =	$(PREFIX)/lib
INSTALL_INCDIR =	$(PREFIX)/include/asdl

INSTALL =		/usr/bin/install -c

CXX =			g++
CXXFLAGS =		-g -O2 -fPIC
CPPFLAGS =		 -I/opt/local/include -Iinclude

LD_STATIC =		/usr/bin/ld
LD_DYNAMIC =		g++ -shared

TARGETS =		libasdl.so

SRCS =          	asdl.cxx
OBJS =          	$(patsubst %.cxx,%.o,$(SRCS))

.PHONY:		build local-install install

build:		$(TARGETS)

libasdl.so:	$(OBJS)
	$(LD_DYNAMIC) -r -o $@ $(OBJS)

%.o : %.cxx
	$(CXX) -c $(CPPFLAGS) $(CXXFLAGS) $<

local-install:	$(TARGETS)
	$(INSTALL) -d $(ASDL_LIBDIR)
	$(INSTALL) -C -m 755 $(TARGETS) $(ASDL_LIBDIR)
	$(INSTALL) -d $(ASDL_INCDIR)
	$(INSTALL) -C -m 644 include/asdl/*hxx $(ASDL_INCDIR)
	$(INSTALL) -C -m 644 include/asdl/config.h $(ASDL_INCDIR)

install:	$(TARGETS)
	$(INSTALL) -d $(INSTALL_LIBDIR)
	$(INSTALL) -C -m 755 $(TARGETS) $(INSTALL_LIBDIR)
	$(INSTALL) -d $(INSTALL_INCDIR)
	$(INSTALL) -C -m 644 include/asdl/*hxx $(INSTALL_INCDIR)
	$(INSTALL) -C -m 644 include/asdl/config.h $(INSTALL_INCDIR)

#################### Cleanup ####################

CLEAN_FILES =		$(OBJS) $(TARGETS)

DISTCLEAN_FILES +=      Makefile

DEVCLEAN_FILES =

include /home/biga/lsu/classes/csc7101/prog2/sml/asdl/mk/clean-rules.gmk
