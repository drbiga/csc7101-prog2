# Makefile for asdlgen tool (using SML/NJ)
#
# This code is part of the SML/NJ system (http://smlnj.org)
#
# COPYRIGHT (c) 2018 The Fellowship of SML/NJ
# All rights reserved.
#
# src/asdlgen/Makefile.  Generated from Makefile.in by configure.
#

SHELL =			/bin/sh

INSTALL =		/usr/bin/install -c

#
# paths to local installation directories
#
ASDL_BINDIR =		/home/biga/lsu/classes/csc7101/prog2/sml/asdl/bin

#
# paths to installation directories
#
PREFIX =		/home/biga/lsu/classes/csc7101/prog2/sml
INSTALL_BINDIR =	$(PREFIX)/bin

#
# paths to commands
#
SML =			/home/biga/lsu/classes/csc7101/prog2/sml/bin/sml
ML_BUILD =		/home/biga/lsu/classes/csc7101/prog2/sml/bin/ml-build
ML_BUILD_FLAGS =
ML_MAKEDEPEND =		/home/biga/lsu/classes/csc7101/prog2/sml/bin/ml-makedepend
ML_MAKEDEPEND_FLAGS =
INSTALL_WRAPPER =	/home/biga/lsu/classes/csc7101/prog2/sml/asdl/bin/install-sml-wrapper.sh

# if specified, include the size option as an argument to ml-build
#
ifneq (64,)
ML_BUILD_FLAGS +=	-64
ML_MAKEDEPEND_FLAGS +=	-64
endif

#
# generator tools
#
MKMK =			/home/biga/lsu/classes/csc7101/prog2/sml/asdl/src/gen/fragments/mkmk.sh
MKFRAGS =		/home/biga/lsu/classes/csc7101/prog2/sml/asdl/src/gen/fragments/mkfrags.sh

PROGRAM =		asdlgen
HEAP =			$(PROGRAM).amd64-linux
ROOT_CM =		driver/sources.cm
CM_FILES =		back-end/sml/sources.cm \
			back-end/sources.cm \
			back-end/util/sources.cm \
			common/sources.cm \
			driver/sources.cm \
			front-end/common/sources.cm \
			front-end/parser/sources.cm \
			front-end/sources.cm \
			front-end/tests/sources.cm \
			front-end/typechecker/sources.cm

CODE_FRAG_DIRS =	back-end/sml

CODE_FRAG_FILES =	$(patsubst %,%/fragments.sml,$(CODE_FRAG_DIRS))
CODE_FRAG_MKFILES =	$(patsubst %,%/fragments.gmk,$(CODE_FRAG_DIRS))

SRCDIR =		/home/biga/lsu/classes/csc7101/prog2/sml/asdl/src/asdlgen

TARGET =		$(SRCDIR)/$(PROGRAM)
HEAP =			$(TARGET).amd64-linux


.PHONY:		build local-install install \
		clean local-distclean local-devclean

build:		$(HEAP)

local-install:	$(HEAP)
	$(INSTALL_WRAPPER) $(TARGET) $(ASDL_BINDIR)

install:	$(HEAP)
	$(INSTALL_WRAPPER) $(TARGET) $(INSTALL_BINDIR)

$(HEAP):  .depend $(CODE_FRAG_MKFILES)
	$(ML_BUILD) $(ML_BUILD_FLAGS) driver/sources.cm Main.main $(PROGRAM)

#
# Rules for generating the fragment dependency and source files
#

back-end/sml/fragments.gmk: back-end/sml/fragments/CATALOG $(wildcard back-end/sml/fragments/*in)
	$(MKMK) back-end/sml

back-end/sml/fragments.sml:
	$(MKFRAGS) back-end/sml

#
# Dependency file rules
#
.depend:        $(CM_FILES) $(CODE_FRAG_FILES)
	touch .depend
	$(ML_MAKEDEPEND) $(ML_MAKEDEPEND_FLAGS) -n -f .depend $(ROOT_CM) $(HEAP) || rm -f .depend

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),devclean)
ifneq ($(MAKECMDGOALS),distclean)
sinclude .depend
sinclude back-end/sml/fragments.gmk
endif
endif
endif

#################### Cleanup ####################

CLEAN_SUBDIRS =

CLEAN_FILES +=          $(HEAP_IMAGE) \
                        front-end/parser/*.grm.sml \
                        front-end/parser/*.lex.sml \
			$(CODE_FRAG_FILES) \
			$(CODE_FRAG_MKFILES) \
                        .depend

DISTCLEAN_FILES +=      Makefile \
                        common/config.sml

DEVCLEAN_FILES =

include /home/biga/lsu/classes/csc7101/prog2/sml/asdl/mk/clean-rules.gmk
