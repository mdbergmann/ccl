/*
 * Copyright 2024 Clozure Associates
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

	include(lisp.s)

	_beginfile

/* Group 1: Core Utilities */

_exportfn(C(current_stack_pointer))
	__(mov x0, sp)
	__(ret)
_endfn

_exportfn(C(count_leading_zeros))
	__(clz x0, x0)
	__(ret)
_endfn

_exportfn(C(noop))
	__(ret)
_endfn

_exportfn(C(touch_page))
	__(ldr x1, [x0])
	__(str x1, [x0])
	__(mov x0, #1)
	.globl C(touch_page_end)
C(touch_page_end):
	__(ret)
_endfn

/* Group 2: Cache Management */

/* Flush D-cache and invalidate I-cache for a memory range.
   x0 = addr, x1 = nbytes */
_exportfn(C(flush_cache_lines))
	__(add x1, x0, x1)		/* x1 = end address */
	__(mrs x2, ctr_el0)		/* read cache type register */
	__(ubfx x3, x2, #16, #4)	/* extract DminLine (log2 words) */
	__(mov x4, #4)
	__(lsl x4, x4, x3)		/* x4 = D-cache line size in bytes */
	__(sub x5, x4, #1)
	__(bic x0, x0, x5)		/* align start down to cache line */
0:
	__(dc cvau, x0)
	__(ic ivau, x0)
	__(add x0, x0, x4)
	__(cmp x0, x1)
	__(b.lo 0b)
	__(dsb ish)
	__(isb)
	__(ret)
_endfn

/* Group 3: Atomic Operations */

/* Atomically store new value (x2) in *x0, if old value == expected (x1).
   Return actual old value in x0. */
_exportfn(C(store_conditional))
0:	__(ldaxr x3, [x0])
	__(cmp x3, x1)
	__(b.ne 1f)
	__(stlxr w4, x2, [x0])
	__(cbnz w4, 0b)
1:	__(mov x0, x3)
	__(ret)
_endfn

/* Atomically store new_value (x1) in *x0; return previous contents
   of *x0. */
_exportfn(C(atomic_swap))
0:	__(ldxr x2, [x0])
	__(stxr w3, x1, [x0])
	__(cbnz w3, 0b)
	__(mov x0, x2)
	__(ret)
_endfn

/* Logior the value in *x0 with the value in x1 (presumably a bitmask
   with exactly 1 bit set.)  Return non-zero if any of the bits in
   that bitmask were already set. */
_exportfn(C(atomic_ior))
0:	__(ldxr x2, [x0])
	__(orr x3, x2, x1)
	__(stxr w4, x3, [x0])
	__(cbnz w4, 0b)
	__(and x0, x2, x1)
	__(ret)
_endfn

/* Logand the value in *x0 with the value in x1.  Return the new
   value in *x0. */
_exportfn(C(atomic_and))
0:	__(ldxr x2, [x0])
	__(and x3, x2, x1)
	__(stxr w4, x3, [x0])
	__(cbnz w4, 0b)
	__(mov x0, x3)
	__(ret)
_endfn

/* Group 4: Memory Barriers */

_exportfn(C(dmb))
	__(dmb sy)
	__(ret)
_endfn

_exportfn(C(dsb))
	__(dsb sy)
	__(ret)
_endfn

_exportfn(C(isb))
	__(isb)
	__(ret)
_endfn

/* Group 5: FP/Vector Context Stubs */

_exportfn(C(save_fp_context))
	__(ret)
_endfn

_exportfn(C(restore_fp_context))
	__(ret)
_endfn

_exportfn(C(put_vector_registers))
	__(ret)
_endfn

_exportfn(C(get_vector_registers))
	__(ret)
_endfn

/* Group 6: Platform-Specific */

	__ifdef(`DARWIN')
_exportfn(C(pseudo_sigreturn))
	__(uuo_pseudo_sigreturn())
	__(b C(pseudo_sigreturn))
_endfn
	__endif

/* call_handler_on_main_stack(signo, info, xp, new_sp, handler)
   x0=signo, x1=info, x2=xp stay intact for the handler.
   x3=new_sp is used to switch the stack.
   x4=handler is the address to jump to. */
_exportfn(C(call_handler_on_main_stack))
	__(mov sp, x3)
	__(br x4)
_endfn

	_endfile
