#
# Copyright 2010 Clozure Associates
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

VC_REVISION := "$(shell git describe --dirty 2>/dev/null || echo unknown)"

OSVERSION=11.0

VPATH = ..
RM = /bin/rm
CC = cc
AS = as
M4 = gm4

M4FLAGS = -DDARWIN -DARM64
ASFLAGS = -arch arm64 -g
CDEFINES = -DDARWIN -DARM64 -DVC_REVISION=$(VC_REVISION)
CDEBUG = -g
COPT = -O
# Once in a while, -Wformat says something useful.  The odds are against that,
# however.
WFORMAT = -Wno-format
PLATFORM_H = platform-darwinarm64.h

.s.o:
	$(M4) $(M4FLAGS) -I../ $< | $(AS) $(ASFLAGS) -mmacosx-version-min=$(OSVERSION) -o $@ -
.c.o:
	$(CC) -include ../$(PLATFORM_H) -c $< -arch arm64 $(CDEFINES) \
	$(CDEBUG) $(COPT) $(WFORMAT) \
	 -I. -mmacosx-version-min=$(OSVERSION) -o $@

SPOBJ = pad.o arm64-spentry.o
ASMOBJ = arm64-asmutils.o imports.o

COBJ  = pmcl-kernel.o gc-common.o arm64-gc.o bits.o arm64-exceptions.o \
	thread_manager.o lisp-debug.o image.o memory.o unix-calls.o \
	mach-o-image.o

DEBUGOBJ = lispdcmd.o plprint.o plsym.o albt.o arm64_print.o
KERNELOBJ= imports.o $(COBJ) arm64-asmutils.o mach_exc_server.o

SPINC =	lisp.s m4macros.m4 arm64-constants.s arm64-macros.s errors.s arm64-uuo.s \
	lisp_globals.s

CHEADERS = area.h bits.h arm64-constants.h lisp-errors.h gc.h lisp.h \
	lisp-exceptions.h lisp_globals.h macros.h memprotect.h image.h \
	threads.h arm64-exceptions.h lisptypes.h \
	$(PLATFORM_H) constants.h os-darwin.h

KSPOBJ= $(SPOBJ)
all:	../../darmcl64

../../darmcl64:	 $(KSPOBJ) $(KERNELOBJ) $(DEBUGOBJ) Makefile
	cc -mmacosx-version-min=$(OSVERSION) -arch arm64 \
	 -o $@ $(SPOBJ) $(KERNELOBJ) $(DEBUGOBJ)

$(SPOBJ): $(SPINC)
$(ASMOBJ): $(SPINC)
$(COBJ): $(CHEADERS)
$(DEBUGOBJ): $(CHEADERS) lispdcmd.h

thread_manager.o: thread_manager.c

mach_exc_server.o: mach_exc_server.c mach_exc.h

mach_exc_server.c: mach_exc.defs
	mig -arch arm64 -header /dev/null -user /dev/null \
		-sheader mach_exc.h -server mach_exc_server.c \
		 $<

mach_exc.h: mach_exc_server.c

cclean:
	$(RM) -f $(KERNELOBJ) $(DEBUGOBJ) ../../darmcl64 \
	  mach_exc.h mach_exc_server.c

clean:	cclean
	$(RM) -f $(SPOBJ) $(KSPOBJ)

strip:	../../darmcl64
	strip -s retain ../../darmcl64
