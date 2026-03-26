/*
 * Copyright 1994-2009 Clozure Associates
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

#ifndef __memprotect_h__
#define __memprotect_h__



#include <signal.h>
#ifndef WINDOWS
#ifdef DARWIN
#include <sys/ucontext.h>
#else
#ifndef ANDROID
#include <ucontext.h>
#endif
#endif
#endif

#ifdef WINDOWS
#define MAP_FAILED ((void *)(-1))

#define MEMPROTECT_NONE PAGE_NOACCESS
#define MEMPROTECT_RO   PAGE_READONLY
#define MEMPROTECT_RW   PAGE_READWRITE
#define MEMPROTECT_RX   PAGE_EXECUTE_READ
#define MEMPROTECT_RWX  PAGE_EXECUTE_READWRITE

#else

#define MEMPROTECT_NONE PROT_NONE
#define MEMPROTECT_RO   PROT_READ
#define MEMPROTECT_RW   (PROT_READ|PROT_WRITE)
#define MEMPROTECT_RX   (PROT_READ|PROT_EXEC)
#ifdef ARM64
/* macOS ARM64 enforces W^X: pages cannot be simultaneously writable
   and executable.  Map as RW for now; proper JIT support will use
   MAP_JIT + pthread_jit_write_protect_np(). */
#define MEMPROTECT_RWX  (PROT_READ|PROT_WRITE)
#else
#define MEMPROTECT_RWX  (PROT_READ|PROT_WRITE|PROT_EXEC)
#endif


#endif

LogicalAddress
ReserveMemoryForHeap(LogicalAddress want, natural totalsize);
LogicalAddress
ReserveMemory(natural totalsize);

int
CommitMemory (LogicalAddress start, natural len);

void
UnCommitMemory (LogicalAddress start, natural len);

LogicalAddress
MapMemory(LogicalAddress addr, natural nbytes, int protection);

LogicalAddress
MapMemoryForStack(natural nbytes);

#if defined(DARWIN) && defined(ARM64)
LogicalAddress
MapMemoryForCode(natural nbytes);
#endif

int
UnMapMemory(LogicalAddress addr, natural nbytes);

int
ProtectMemory(LogicalAddress, natural);

int
UnProtectMemory(LogicalAddress, natural);

int
MapFile(LogicalAddress addr, natural pos, natural nbytes, int permissions, int fd);
void allocation_failure(Boolean pointerp, natural size);

void protect_watched_areas(void);
void unprotect_watched_areas(void);

typedef enum {
  kNotProtected,		/* At least not at the moment. */
  kVSPsoftguard,
  kSPsoftguard,
  kTSPsoftguard,
  kSPhardguard,			/* Touch one and die. */
  kVSPhardguard,
  kTSPhardguard,
  kHEAPsoft,			/* Uninitialized page in the heap */
  kHEAPhard,			/* The end-of-the-line in the heap */
  /* Phony last entry. */
  kNumProtectionKinds
  } lisp_protection_kind;

typedef
struct protected_area {
  struct protected_area *next;
  BytePtr start;                /* first byte (page-aligned) that might be protected */
  BytePtr end;                  /* last byte (page-aligned) that could be protected */
  unsigned nprot;               /* Might be 0 */
  unsigned protsize;            /* number of bytes to protect */
  lisp_protection_kind why;
} protected_area, *protected_area_ptr;

void unprotect_area(protected_area_ptr);

/* Various functions that try to respond to a protection violation */
typedef 
  OSStatus (protection_handler)(ExceptionInformation *, protected_area_ptr, BytePtr);

protection_handler 
  do_spurious_wp_fault,
  do_soft_stack_overflow,
  do_hard_stack_overflow,
  do_tenured_space_write,
  do_heap_soft_probe,
  do_heap_hard_probe;

extern protection_handler
  *protection_handlers[];


void
exception_cleanup(void);


void
initialize_refidx_from_refbits(bitvector, bitvector, natural);

#if defined(DARWIN) && defined(ARM64)
#include <pthread.h>
#include <sys/mman.h>
#include <libkern/OSCacheControl.h>
#include <mach/mach.h>

/* Separate code area (AREA_CODE) with dual mapping for ARM64 W^X.
   The code area has two virtual addresses for the same physical pages:
   - RW mapping (code_area->low): always writable, used for allocation & data writes
   - RX mapping (code_area_rx_base): always executable, used for function entrypoints
   This avoids MAP_JIT's per-thread W^X toggle, which makes the calling
   code non-executable when toggled to writable. */

extern BytePtr code_area_rx_base;   /* RX mirror base address */
extern natural code_rw_rx_bias;     /* rx_base - rw_base, for assembly */

/* No-op toggles — dual mapping means RW and RX are always available */
static inline void code_area_make_writable(void) { }
static inline void code_area_make_executable(void) { }

static inline void code_area_flush_icache(void *addr, natural nbytes) {
  sys_icache_invalidate(addr, nbytes);
}

/* Convert RW address to RX address and vice versa.
   Uses the precomputed bias (rx_base - rw_base). */
static inline natural code_rw_to_rx(natural rw_addr) {
  return rw_addr + code_rw_rx_bias;
}

static inline natural code_rx_to_rw(natural rx_addr) {
  return rx_addr - code_rw_rx_bias;
}

/* Code vector allocator — called from Lisp via kernel import */
natural alloc_code_vector(natural element_count);
void make_code_vector_executable(natural addr);

#endif

#endif /* __memprotect_h__ */
