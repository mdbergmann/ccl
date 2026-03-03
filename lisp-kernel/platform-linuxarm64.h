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
#define PLATFORM_OS PLATFORM_OS_LINUX
#define PLATFORM_CPU PLATFORM_CPU_ARM64
#define PLATFORM_WORD_SIZE PLATFORM_WORD_SIZE_64

#include <ucontext.h>

typedef ucontext_t ExceptionInformation;

#define MAXIMUM_MAPPABLE_MEMORY (512L<<30L)
#define IMAGE_BASE_ADDRESS 0x300000000000L

#include "lisptypes.h"
#include "arm64-constants.h"

/* xp accessors — Linux AArch64 ucontext_t.
   uc_mcontext.regs[] is an array of 31 uint64_t (x0-x30).
   uc_mcontext.sp, .pc, .pstate are separate fields. */
#define xpGPRvector(x) ((natural *)(&((x)->uc_mcontext.regs[0])))
#define xpGPR(x,gprno) (xpGPRvector(x)[gprno])
#define set_xpGPR(x,gpr,new) xpGPR((x),(gpr)) = (natural)(new)
#define xpPC(x) (*((pc *)(&((x)->uc_mcontext.pc))))
#define xpLR(x) (*((pc *)(&((x)->uc_mcontext.regs[30]))))
#define xpSP(x) ((x)->uc_mcontext.sp)
#define xpPSR(x) ((x)->uc_mcontext.pstate)
#define xpFaultAddress(x) ((x)->uc_mcontext.fault_address)

#define SIGNUM_FOR_INTN_TRAP SIGTRAP
#define IS_PAGE_FAULT(info,xp) ((info)->si_signo == SIGSEGV || (info)->si_signo == SIGBUS)

#define DarwinSigReturn(context)
#define SIGRETURN(context)

#include "os-linux.h"

#define PROTECT_CSTACK 1
