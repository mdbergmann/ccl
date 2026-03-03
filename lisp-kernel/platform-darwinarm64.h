/*
 * Copyright 2016 Clozure Associates
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#define WORD_SIZE 64
#define PLATFORM_OS PLATFORM_OS_DARWIN
#define PLATFORM_CPU PLATFORM_CPU_ARM64
#define PLATFORM_WORD_SIZE PLATFORM_WORD_SIZE_64

#define _DARWIN_C_SOURCE

#include <sys/signal.h>
#include <sys/ucontext.h>

typedef mcontext_t MCONTEXT_T;
typedef ucontext_t ExceptionInformation;
#define UC_MCONTEXT(UC) UC->uc_mcontext

#define MAXIMUM_MAPPABLE_MEMORY (512L<<30L)
#define IMAGE_BASE_ADDRESS 0x300000000000L

#include "lisptypes.h"
#include "arm64-constants.h"

/* xp accessors — Darwin AArch64 ucontext.
   __arm_thread_state64.__x[] has 29 entries (x0-x28).
   __fp (x29), __lr (x30) are contiguous in memory, so indexing
   through __x[0] with gprno 0-30 works for all GPRs. */
#define xpGPRvector(x) ((natural *)(&(UC_MCONTEXT(x)->__ss.__x[0])))
#define xpGPR(x,gprno) (xpGPRvector(x)[gprno])
#define set_xpGPR(x,gpr,new) xpGPR((x),(gpr)) = (natural)(new)
#define xpPC(x) (*((pc *)(&(UC_MCONTEXT(x)->__ss.__pc))))
#define xpLR(x) (*((pc *)(&(UC_MCONTEXT(x)->__ss.__lr))))
#define xpSP(x) (UC_MCONTEXT(x)->__ss.__sp)
#define xpFP(x) (UC_MCONTEXT(x)->__ss.__fp)
#define xpPSR(x) (UC_MCONTEXT(x)->__ss.__cpsr)
#define xpFaultAddress(x) (UC_MCONTEXT(x)->__es.__far)
#define xpFaultStatus(x) (UC_MCONTEXT(x)->__es.__esr)

#define SIGNUM_FOR_INTN_TRAP SIGTRAP
#define IS_PAGE_FAULT(info,xp) ((info)->si_signo == SIGSEGV || (info)->si_signo == SIGBUS)

/* Darwin ARM64 sigreturn — empty for now, will be refined
   when arm64-exceptions.c is implemented. */
#define DarwinSigReturn(context)
#define SIGRETURN(context)

#include <mach/mach.h>
#include <mach/mach_error.h>
#include <mach/machine/thread_state.h>
#include <mach/machine/thread_status.h>

#include "os-darwin.h"
