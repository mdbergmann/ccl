/*
 * Copyright 2012 Clozure Associates
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
	.align 2



local_label(start):
define(`_spentry',`ifdef(`__func_name',`_endfn',`')
	_startfn(_SP$1)
L__SP$1:
	.line  __line__
')


define(`_endsubp',`
	_endfn(_SP$1)
# __line__
')


	

define(`jump_builtin',`
        __(ref_nrs_value(fname,builtin_functions))
	__(set_nargs($2))
	__(ldr fname,[fname,#$1*8])
	__(jump_fname())
')




/* Fix the entrypoint of the function in nfn.  Copy the code-vector
   pointer from slot 1 into slot 0 (the entrypoint slot), then
   re-enter the function through its now-valid entrypoint.
   This is called when a newly-created closure is invoked for the
   first time — its entrypoint initially points here.
   Must be the first entry in the subprims table.
   Bug 128: Must strip TBI tag — br/blr do NOT honor TBI on macOS ARM64.
   Bug 152: temp2=nfn=x10 on ARM64 — must use a different register (imm0)
   to avoid clobbering nfn and corrupting the code vector. */
_spentry(fix_nfn_entrypoint)
        __(ldr imm0,[nfn,#node_size])              /* load slot 1 = code vector (tagged) */
        __(and imm0,imm0,#0x00FFFFFFFFFFFFFF)      /* strip TBI tag for br/blr */
        __(str imm0,[nfn,#_function.entrypoint])    /* store untagged into slot 0 */
        __(br imm0)                                 /* branch to code, nfn preserved */
_endsubp(fix_nfn_entrypoint)


_spentry(builtin_plus)
        __(add imm0,arg_y,arg_z)
        __(sbfx imm1,imm0,#0,#56)
        __(cmp imm1,imm0)
        __(bne 0f)
        __(mov arg_z,imm0)
        __(ret)
0:      __(extract_tag(imm1,imm0))
        __(cmp imm1,#tag_overflowed_negative_fixnum)
        __(ccmp imm1,#tag_overflowed_positive_fixnum,#nzvc_z,ne)
        __(bne 1f)
        __(mov imm1,#2)
        __(orr imm1,imm1,#bignum_header<<tag_shift)
        __(mov temp0,#tag_bignum)
        __(Misc_Alloc_Fixed(arg_z,imm1,aligned_bignum_size(1),temp0))
        __(str imm0,[arg_z,#0])
        __(ret)
1:
	__(jump_builtin(_builtin_plus,2))
        
_spentry(builtin_minus)
        __(sub imm0,arg_y,arg_z)
        __(sbfx imm1,imm0,#0,#56)
        __(cmp imm1,imm0)
        __(bne 0f)
        __(mov arg_z,imm0)
        __(ret)
0:      __(extract_tag(imm1,imm0))
        __(cmp imm1,#tag_overflowed_negative_fixnum)
        __(ccmp imm1,#tag_overflowed_positive_fixnum,#nzvc_z,ne)
        __(bne 1f)
        __(mov imm1,#2)
        __(orr imm1,imm1,#bignum_header<<tag_shift)
        __(mov imm2,#tag_bignum)
        __(Misc_Alloc_Fixed(arg_z,imm1,aligned_bignum_size(1),imm2))
        __(str imm0,[arg_z,#0])
        __(ret)
1:
	__(jump_builtin(_builtin_minus,2))

_spentry(builtin_times)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(mul imm0,arg_y,arg_z)
        __(smulh imm1,arg_y,arg_z)
        __(b _SPmakes128)
1:      __(jump_builtin(_builtin_times,2))

_spentry(builtin_div)
        __(jump_builtin(_builtin_div,2))

_spentry(builtin_eq)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
	__(cmp arg_y,arg_z)
        __(lisp_boolean(arg_z,eq))
	__(ret)
1:
	__(jump_builtin(_builtin_eq,2))
                        
_spentry(builtin_ne)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
	__(cmp arg_y,arg_z)
        __(lisp_boolean(arg_z,ne))
	__(ret)
1:
	__(jump_builtin(_builtin_ne,2))

_spentry(builtin_gt)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
	__(cmp arg_y,arg_z)
        __(lisp_boolean(arg_z,gt))
        __(ret)
1:
	__(jump_builtin(_builtin_gt,2))

_spentry(builtin_ge)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
	__(cmp arg_y,arg_z)
        __(lisp_boolean(arg_z,ge))
        __(ret)
1:
	__(jump_builtin(_builtin_ge,2))

_spentry(builtin_lt)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
	__(cmp arg_y,arg_z)
        __(lisp_boolean(arg_z,lt))
        __(ret)
1:
	__(jump_builtin(_builtin_lt,2))

_spentry(builtin_le)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
	__(cmp arg_y,arg_z)
        __(lisp_boolean(arg_z,le))
        __(ret)
1:
	__(jump_builtin(_builtin_le,2))

_spentry(builtin_eql)
0:      __(cmp arg_y,arg_z)
        __(beq 8f)
        __(extract_tag(imm0,arg_y))
        __(extract_tag(imm1,arg_z))
        __(cmp imm0,imm1)
        __(bne 9f)
        __(mov imm1,#subtag_double_float)
        __(cmp imm0,#subtag_macptr)
        __(ccmp imm0,imm1,#nzvc_z,ne)
        __(bne 2f)
        __(ldr imm0,[arg_y,#0])
        __(ldr imm1,[arg_z,#0])
        __(cmp imm0,imm1)
        __(lisp_boolean(arg_z,eq))
        __(ret)
2:      __(mov imm1,#subtag_ratio)      /* value won't fit in ccmp operand */
        __(cmp imm0,#subtag_complex)
        __(ccmp imm0,imm1,#nzvc_z,ne)
        __(bne 3f)
        __(ldr temp0,[arg_y,#ratio.denom])
        __(ldr temp1,[arg_z,#ratio.denom])
        __(stp temp0,temp1,[vsp,#-2*node_size]!)
        __(ldr arg_y,[arg_y,#ratio.numer])
        __(ldr arg_z,[arg_z,#ratio.numer])
        __(build_lisp_frame())
        __(bl 0b)
        __(cmp arg_z,rnil)
        __(restore_lisp_frame())
        __(ldp arg_z,arg_y,[vsp],#2*node_size)
        __(bne 0b)
        __(mov arg_z,rnil)
        __(ret)
3:      __(cmp imm0,#subtag_bignum)
        __(bne 9f)
        __(getvheader(imm0,arg_y))
        __(getvheader(imm1,arg_z))
        __(cmp imm0,imm1)
        __(bne 9f)
        __(header_length(temp0,imm0))
        __(mov imm2,#0)
4:      __(ldr gpr32(imm0),[arg_y,imm2,lsl #2])
        __(ldr gpr32(imm1),[arg_z,imm2,lsl #2])
        __(cmp imm0,imm1)
        __(bne 9f)
        __(add imm2,imm2,#4)
        __(subs temp0,temp0,#fixnumone)
        __(bne 4b)                
8:      __(mov arg_z,rt)
        __(ret)
9:      __(mov arg_z,rnil)
        __(ret)
        
_spentry(builtin_length)
        __(branch_if_list(arg_z,6f,imm0))
        __(extract_tag(imm0,arg_z))
        __(cmp imm0,#tag_simple_vector)
        __(beq 0f)
        __(cmp imm0,#tag_vectorH)
        __(beq 1f)
        __(and imm1,imm0,#uvector_mask)
        __(cmp imm1,#uvector_ref)
        __(b.ne 8f)
        __(tbnz imm0,#gvector_tag_bit,8f)
        __(tbz imm0,#cl_ivector_tag_bit,8f)
0:      __(vector_length(arg_z,arg_z,imm0))
        __(ret)
1:      __(ldr arg_z,[arg_z,#vectorH.logsize])
        __(ret)
6:      __(mov temp2,#-1)
        __(mov temp0,arg_z) /* fast pointer  */
        __(mov temp1,arg_z) /* slow pointer  */
7:      __(cmp temp0,rnil)
        __(add temp2,temp2,#1)
        __(b.eq 9f)
        __(branch_if_not_list(temp0,8f,imm0,imm0))
        __(_cdr(temp0,temp0))
        __(tst temp2,#1)
        __(b.eq 7b)
        __(_cdr(temp1,temp1))
        __(cmp temp1,temp0)
        __(b.ne 7b)
8: 
        __(jump_builtin(_builtin_length,1))
9:      __(mov arg_z,temp2)
        __(ret)       

_spentry(builtin_seqtype)
        __(branch_if_list(arg_z,1f,imm0))
        __(extract_tag(imm0,arg_z))
        __(cmp imm0,#tag_simple_vector)
        __(beq 0f)
        __(cmp imm0,#tag_vectorH)
        __(beq 0f)
        __(and imm1,imm0,#uvector_mask)
        __(cmp imm1,#uvector_ref)
        __(bne 2f)
        __(tbnz imm0,#gvector_tag_bit,2f)
        __(tbz imm0,#cl_ivector_tag_bit,2f)
0:      __(mov arg_z,rnil)
        __(ret)
1:      __(mov arg_z,rt)
        __(ret)        
2:      __(jump_builtin(_builtin_seqtype,1))

/* This is usually inlined these days */
_spentry(builtin_assq)
        __(b 2f)
1:      __(trap_unless_list(arg_z,imm0))
        __(_car(arg_x,arg_z))
        __(_cdr(arg_z,arg_z))
        __(cmp arg_x,rnil)
        __(beq 2f)
        __(trap_unless_list(arg_x,imm0))
        __(_car(temp0,arg_x))
        __(cmp temp0,arg_y)
        __(bne 2f)
        __(mov arg_z,arg_x)
        __(ret)
2:      __(cmp arg_z,rnil)
        __(bne 1b)
        __(ret)
 
_spentry(builtin_memq)
        __(cmp arg_z,rnil)
        __(b 2f)
1:      __(trap_unless_list(arg_z,imm0))
        __(_car(arg_x,arg_z))
        __(_cdr(temp0,arg_z))
        __(cmp arg_x,arg_y)
        __(b.eq 3f)
        __(cmp temp0,rnil)
        __(mov arg_z,temp0)
2:      __(b.ne 1b)
3:      __(ret)

_spentry(builtin_logbitp)
/* Call out unless both fixnums,0 <=  arg_y < logbitp_max_bit  */
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(branch_if_negative(arg_y,1f))
        __(mov imm0,#63)
        __(cmp arg_y,imm0)
        __(csel arg_y,imm0,arg_y,gt)
        __(lsr imm0,arg_z,arg_y)
        __(tst imm0,#1)
        __(lisp_boolean(arg_z,ne))
        __(ret)
1:
        __(jump_builtin(_builtin_logbitp,2))

_spentry(builtin_logior)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(orr arg_z,arg_y,arg_z)
        __(ret)
1:              
        __(jump_builtin(_builtin_logior,2))

_spentry(builtin_logand)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(and arg_z,arg_y,arg_z)
        __(ret)
1:              
        __(jump_builtin(_builtin_logand,2))
          
_spentry(builtin_ash)
        __(branch_if_not_fixnum(arg_y,9f,imm0))
        __(branch_if_not_fixnum(arg_z,9f,imm0))
        __(branch_if_negative(arg_z,0f))
        __(cbnz arg_z,1f)
        __(mov arg_z,arg_y)
        __(ret)
0:              
        /* Shift right */
        __(neg imm2,arg_z)
        __(mov imm1,#63)
        __(cmp imm2,imm1)
        __(csel imm2,imm1,imm2,gt)
        __(asr arg_z,arg_y,imm2)
        __(ret)
        /* shift left */
1:      __(mov imm0,arg_y)
        __(mov imm2,arg_z)
        __(cmp imm2,#64)
        __(csel imm1,imm0,imm1,eq)
        __(csel imm0,xzr,imm0,eq)
        __(beq _SPmakes128)
        __(bgt 9f)
        __(mov imm1,#64)
        __(sub imm1,imm1,imm2)
        __(asr imm1,imm0,imm1)
        __(lsl imm0,imm0,imm2)
        __(b _SPmakes128)
9:  
        __(jump_builtin(_builtin_ash,2))
                                	
_spentry(builtin_negate)
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(neg arg_z,arg_z)
        __(branch_if_not_fixnum(arg_z,_SPfix_overflow,imm0))
        __(ret)
1:
        __(jump_builtin(_builtin_negate,1))
 
_spentry(builtin_logxor)
        __(branch_if_not_fixnum(arg_y,1f,imm0))
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(eor arg_z,arg_y,arg_z)
        __(ret)
1:              
        __(jump_builtin(_builtin_logxor,2))

/* Bug 164: builtin_aref1/aset1 extract the TBI reference tag via
   extract_tag (lsr #56), but subtag_misc_ref/set expect the HEADER
   subtag in arg_x/temp0.  Reference tag has bit 6 set (uvector_ref=0x40);
   header subtag has bit 7 set (uvector_header=0x80).  Convert by
   XORing with uvector_mask (0xC0) before calling subtag_misc_ref/set. */
_spentry(builtin_aref1)
        __(extract_tag(arg_x,arg_y))
        __(cmp arg_x,#tag_simple_vector)
        __(beq 1f)
        __(and imm0,arg_x,#uvector_mask)
        __(cmp imm0,#uvector_ref)
        __(bne 0f)
        __(tbnz arg_x,#gvector_tag_bit,0f)
        __(tbnz arg_x,#cl_ivector_tag_bit,1f)
0:      __(jump_builtin(_builtin_aref1,2))
1:      __(eor arg_x,arg_x,#uvector_mask)
        __(b _SPsubtag_misc_ref)

_spentry(builtin_aset1)
        __(extract_tag(temp0,arg_x))
        __(cmp temp0,#tag_simple_vector)
        __(beq 1f)
        __(and imm0,temp0,#uvector_mask)
        __(cmp imm0,#uvector_ref)
        __(bne 0f)
        __(tbnz temp0,#gvector_tag_bit,0f)
        __(tbnz temp0,#cl_ivector_tag_bit,1f)
0:      __(jump_builtin(_builtin_aset1,3))
1:      __(eor temp0,temp0,#uvector_mask)
        __(b _SPsubtag_misc_set)
                	

	/*  Call nfn if it's either a symbol or function */
	/* Bug 158 workaround: tail-funcall-vsp (inline) in existing images
	   doesn't restore x29 from the frame before popping.  After the
	   pop, x29 < sp (stale, pointing at the discarded frame).
	   Detect this and restore x29 from [sp-8] (the discarded frame's
	   savefp slot).  In non-tail cases x29 >= sp, so this is a no-op. */
_spentry(funcall)
	__(mov imm0,sp)
	__(cmp x29,imm0)
	__(bhs 0f)
	__(ldr x29,[sp,#-node_size])
0:
	__(funcall_nfn())

/* Subprims for catch, throw, unwind_protect.  */


_spentry(mkcatch1v)
	__(mov imm2,#0)
	__(mkcatch())
	__(ret)


_spentry(mkcatchmv)
	__(mov imm2,#fixnum_one)
	__(mkcatch())
	__(ret)

_spentry(mkunwind)
        __(mov imm2,#-fixnumone)
        __(mov imm1,#INTERRUPT_LEVEL_BINDING_INDEX)
        __(ldr temp0,[rcontext,#tcr.tlb_pointer])
        __(ldr arg_y,[temp0,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(vpush1(arg_y))
        __(vpush1(imm1))
        __(vpush1(imm0))
        __(str imm2,[temp0,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(str vsp,[rcontext,#tcr.db_link])
        __(mov arg_z,#unbound_marker)
        __(mov imm2,#fixnum_one)
        __(mkcatch())
        __(mov arg_z,arg_y)
        __(b _SPbind_interrupt_level)
        

/* This never affects the symbol's vcell  */
/* Non-null symbol in arg_y, new value in arg_z          */
_spentry(bind)
	__(ldr imm1,[arg_y,#symbol.binding_index])
	/* Bug 124: binding-index is already a byte offset (fixnumshift=0, increment=8) */
	__(ldr imm0,[rcontext,#tcr.tlb_limit])
	__(cmp imm0,imm1)
        __(bhi 1f)
	__(uuo_tlb_too_small(imm1))
1:
	__(cmp imm1,#0)
	__(ldr imm2,[rcontext,#tcr.tlb_pointer])
	__(ldr imm0,[rcontext,#tcr.db_link])
	__(ldr temp1,[imm2,imm1])
	__(beq 9f)
	__(vpush1(temp1))
	__(vpush1(imm1))
	__(vpush1(imm0))
	__(str arg_z,[imm2,imm1])
	__(str vsp,[rcontext,#tcr.db_link])
	__(ret)
9:
	__(mov arg_z,arg_y)
	__(mov arg_y,#XSYMNOBIND)
	__(set_nargs(2))
	__(b _SPksignalerr)

_spentry(conslist)
	__(mov arg_z,rnil)
	__(cmp nargs,#0)
	__(b 2f) 
1:
	__(vpop1(arg_y))
	__(Cons(arg_z,arg_y,arg_z))
	__(subs nargs,nargs,#node_size)
2:
	__(bne 1b)
	__(ret)

/* do list*: last arg in arg_z, all others vpushed, nargs set to #args vpushed.  */
/* Cons, one cons cell at at time.  Maybe optimize this later.  */

_spentry(conslist_star)
	__(cmp nargs,#0)
	__(b 2f)
1:
	__(vpop1(arg_y))
	__(Cons(arg_z,arg_y,arg_z))
	__(subs nargs,nargs,#node_size)
2:
	__(bne 1b)
	__(ret)

_spentry(makes64)
        __(branch_if_not_fixnum(imm0,0f,imm1))
        __(mov arg_z,imm0)
        __(ret)
0:      __(mov imm1,#2)
        __(orr imm1,imm1,#bignum_header<<tag_shift)
        __(mov imm2,#tag_bignum)
        __(Misc_Alloc_Fixed(arg_z,imm1,aligned_bignum_size(2),imm2))
	__(str imm0,[arg_z,#misc_data_offset])
     	__(ret)

/* Construct a lisp integer out of the 64-bit unsigned value in imm0 */


_spentry(makeu64)
        __(clz imm1,imm0)
        __(cmp imm1,#8)
        __(ble 0f)
        __(mov arg_z,imm0)
        __(ret)
0:      __(mov imm2,#tag_bignum)
        __(cbz imm1,1f)
        __(mov imm1,#2)
        __(orr imm1,imm1,#bignum_header<<tag_shift)
        __(Misc_Alloc_Fixed(arg_z,imm1,aligned_bignum_size(2),imm2))
        __(str imm0,[arg_z,#0])
        __(ret)
1:      __(mov imm1,#3)
        __(orr imm1,imm1,#bignum_header<<tag_shift)
        __(Misc_Alloc_Fixed(arg_z,imm1,aligned_bignum_size(3),imm2))
        __(str imm0,[arg_z,#0])
        __(ret)


/* arg_z has overflowed (by one bit) as the result of an addition or
   subtraction. */
/* Make a bignum out of it. */

_spentry(fix_overflow)
        __(mov imm0,arg_z)
	__(b _SPmakes64)



/*  Construct a lisp integer out of the 128-bit unsigned value in */
/*           imm0 (low  bits) and imm1 (high 32 bits) */
	
_spentry(makeu128)
	__(cbz imm1,_SPmakeu64)
        __(mov temp0,#tag_bignum)
	__(branch_if_negative(imm1,5f))
        __(clz imm2,imm1)
        __(cmp imm2,#32)
        __(ble 4f)
	__(make_header(imm2,3,bignum_header))
	__(Misc_Alloc_Fixed(arg_z,imm2,aligned_bignum_size(3),temp0))
	__(str imm0,[arg_z,#misc_data_offset])
        __(str gpr32(imm1),[arg_z,#misc_data_offset+8])
	__(ret)

4:              
	__(make_header(imm2,4,bignum_header))
	__(Misc_Alloc_Fixed(arg_z,imm2,aligned_bignum_size(4),temp0))
	__(str imm0,[arg_z,#misc_data_offset])
	__(str imm1,[arg_z,#misc_data_offset+8])
	__(ret)
5:              
	__(make_header(imm2,5,bignum_header))
	__(Misc_Alloc_Fixed(arg_z,imm2,aligned_bignum_size(5),temp0))
	__(str imm0,[arg_z,#misc_data_offset])
	__(str imm1,[arg_z,#misc_data_offset+8])
	__(ret)

/*  Construct a lisp integer out of the 128-bit signed value in */
/*        imm0 (low 64 bits) and imm1 (high 64 bits). */
_spentry(makes128)
	__(cmp imm1,imm0,asr #63) /* is imm1 sign extension of imm0 ? */
	__(beq _SPmakes64)        /* forget imm1 if so */
        __(mov imm3,#tag_bignum)
        __(asr imm2,imm1,#32)
        __(cmp imm1,imm2,lsl #32)
        __(beq 3f)
	__(mov imm2,#4)
        __(orr imm2,imm2,#bignum_header<<tag_shift)
	__(Misc_Alloc_Fixed(arg_z,imm2,aligned_bignum_size(4),imm3))
	__(str imm0,[arg_z,#misc_data_offset])
	__(str imm1,[arg_z,#misc_data_offset+8])
	__(ret)
3:      
       	__(mov imm2,#3)
        __(orr imm2,imm2,#bignum_header<<tag_shift)
	__(Misc_Alloc_Fixed(arg_z,imm2,aligned_bignum_size(3),imm3))
	__(str imm0,[arg_z,#misc_data_offset])
	__(str gpr32(imm1),[arg_z,#misc_data_offset+8])
	__(ret)






/* funcall nfn, returning multiple values if it does.  */
/* Bug 165 ROOT CAUSE: The csel logic was wrong — for nargs <= nargregs*node_size
   it computed vsp+nargs instead of vsp, and for nargs > nargregs*node_size it
   computed vsp-24 instead of vsp-24+nargs.  This caused return values to be
   placed at wrong vstack positions, overwriting let* bindings.
   Fixed to match SPmvpasssym and ARM32 SPmvpass pattern. */
_spentry(mvpass)
        __(cmp nargs,#node_size*nargregs)
        __(mov imm1,vsp)
        __(ble 0f)
        __(sub imm1,imm1,#node_size*nargregs)
        __(add imm1,imm1,nargs)
0:
        /* Bug 165 diagnostic: check nfn tag before calling */
        __(lsr imm0,nfn,#tag_shift)
        __(cmp imm0,#tag_function)
        __(beq 1f)
        __(cmp imm0,#tag_symbol)
        __(beq 1f)
        /* nfn is not callable — trap with x29 and vsp info intact */
        __(hlt #0xFFD0)     /* Bug 165: nfn invalid in SPmvpass */
1:
	__(build_lisp_frame(imm1))
	__(adr lr,C(ret1valn))
	__(funcall_nfn())

/* ret1valn returns "1 multiple value" when a called function does not  */
/* return multiple values.  Its presence on the stack (as a return address)  */
/* identifies the stack frame to code which returns multiple values.  */

_exportfn(C(ret1valn))
	__(restore_lisp_frame())
	__(vpush1(arg_z))
	__(set_nargs(1))
	__(ret)

/* Come here to return multiple values when  */
/* the caller's context isn't saved in a lisp_frame.  */
/* lr, fn valid; temp0 = entry vsp  */

_spentry(values)
local_label(return_values):  
	__(ref_global(imm0,ret1val_addr))
	__(mov arg_z,rnil)
	__(cmp imm0,lr)
	__(beq 3f)
	__(cmp nargs,#1*node_size)
	__(add imm0,vsp,nargs)
        __(blo 0f)
	__(ldr arg_z,[imm0,#-node_size])
0:
	__(mov vsp,temp0)
	__(ret)


/* Return multiple values to real caller.  */
3:
	__(ldr lr,[sp,#lisp_frame.savelr])
	__(add imm1,vsp,nargs)
	__(ldr imm0,[sp,#lisp_frame.savevsp])
	__(cmp imm1,imm0) /* a fairly common case  */
	__(discard_lisp_frame())
	__(b.eq 9f) /* already in the right place  */
	__(cmp nargs,#1*node_size) /* sadly, a very common case  */
	__(bne 4f)
	__(ldr arg_z,[vsp,#0])
	__(mov vsp,imm0)
	__(vpush1(arg_z))
	__(ret)
4:
	__(blt 6f)
	__(mov temp1,#node_size)
5:
	__(cmp temp1,nargs)
	__(add temp1,temp1,#node_size)
	__(ldr arg_z,[imm1,#-node_size]!)
	__(push1(arg_z,imm0))
	__(bne 5b)
6:
	__(mov vsp,imm0)
9:      __(ret)                 


/* Come here with saved context on top of stack.  */
_spentry(nvalret)
	.globl C(nvalret)
C(nvalret):
	__(ldr lr,[sp,#lisp_frame.savelr])
	__(ldr temp0,[sp,#lisp_frame.savevsp])
	__(discard_lisp_frame())
	__(b local_label(return_values))                         

/* Caller has pushed tag and 0 or more values; nargs = nvalues.  */
/* Otherwise, process unwind-protects and throw to indicated catch frame.  */

                
 _spentry(throw)
        __(ldr temp0,[rcontext, #tcr.catch_top])
        __(mov imm0,#0) /* count intervening catch/unwind-protect frames.  */
        __(cmp temp0,#0)
        __(ldr temp2,[vsp,nargs])
        __(beq local_label(_throw_tag_not_found))
local_label(_throw_loop):
        __(ldr temp1,[temp0,#catch_frame.catch_tag])
        __(cmp temp2,temp1)
        __(beq C(_throw_found))
        __(ldr temp0,[temp0,#catch_frame.link])
        __(cmp temp0,#0)
        __(add imm0,imm0,#fixnum_one)
        __(bne local_label(_throw_loop))
local_label(_throw_tag_not_found):
        __(uuo_error_no_throw_tag(temp2))
        __(str temp2,[vsp,nargs])
        __(b _SPthrow)

/* This takes N multiple values atop the vstack.  */
_spentry(nthrowvalues)
        __(mov imm1,#1)
        __(mov temp2,imm0)
        __(str imm1,[rcontext,#tcr.unwinding])
        __(b C(nthrownv))

/* This is a (slight) optimization.  When running an unwind-protect, */
/* save the single value and the throw count in the tstack frame. */
/* Note that this takes a single value in arg_z.  */
_spentry(nthrow1value)
        __(mov imm1,#1)
        __(mov temp2,imm0)
        __(str imm1,[rcontext,#tcr.unwinding])
        __(b C(nthrow1v))


/* arg_z = symbol: bind it to its current value          */
 _spentry(bind_self)
        __(ldr imm1,[arg_z,#symbol.binding_index])
        /* Bug 124: binding-index is already a byte offset */
        __(ldr imm0,[rcontext,#tcr.tlb_limit])
        __(cmp imm1,#0)
        __(beq 9f)
        __(cmp imm0,imm1)
        __(bhi 1f)
        __(uuo_tlb_too_small(imm1))
1:
        __(ldr temp2,[rcontext,#tcr.tlb_pointer])
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(ldr temp1,[temp2,imm1])
        __(cmp_tag_to_marker(temp1,temp0,tag_no_thread_local_binding))
        __(bne 2f)
        __(ldr temp0,[arg_z,#symbol.vcell])
        __(b 3f)
2:      __(mov temp0,temp1)
3:      __(vpush1(temp1))   /* old tlb contents */
        __(vpush1(imm1))    /* tlb index */
        __(vpush1(imm0))
        __(str temp0,[temp2,imm1])
        __(str vsp,[rcontext,#tcr.db_link])
        __(ret)
9:      __(mov arg_y,#XSYMNOBIND)
        __(set_nargs(2))
        __(b _SPksignalerr)

/* Bind symbol in arg_z to NIL                 */
_spentry(bind_nil)
        __(mov arg_y,arg_z)
        __(mov arg_z,rnil)
        __(b _SPbind)

/* Bind symbol in arg_z to its current value;  trap if symbol is unbound */
_spentry(bind_self_boundp_check)
        __(ldr imm1,[arg_z,#symbol.binding_index])
        /* Bug 124: binding-index is already a byte offset */
        __(ldr imm0,[rcontext,#tcr.tlb_limit])
        __(cmp imm1,#0)
        __(beq 9f)
        __(cmp imm0,imm1)
        __(bhi 1f)
        __(uuo_tlb_too_small(imm1))
1:
        __(ldr temp2,[rcontext,#tcr.tlb_pointer])
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(ldr temp1,[temp2,imm1])
        __(cmp_tag_to_marker(temp1,temp0,tag_no_thread_local_binding))
        __(bne 3f)
        __(ldr temp0,[arg_z,#symbol.vcell])
        __(b 4f)
3:      __(mov temp0,temp1)
4:      __(cmp_tag_to_marker(temp0,imm2,tag_unbound))
        __(bne 2f)
        __(uuo_error_unbound(arg_z))
2:
        __(vpush1(temp1))   /* old tlb contents */
        __(vpush1(imm1))    /* tlb index */
        __(vpush1(imm0))
        __(str temp0,[temp2,imm1])
        __(str vsp,[rcontext,#tcr.db_link])
        __(ret)
9:      __(mov arg_y,#XSYMNOBIND)
        __(set_nargs(2))
        __(b _SPksignalerr)


/* The function pc_luser_xp() - which is used to ensure that suspended threads */
/* are suspended in a GC-safe way - has to treat these subprims (which  */
/* implement the EGC write-barrier) specially.  Specifically, a store that */
/* might introduce an intergenerational reference (a young pointer stored  */
/* in an old object) has to "memoize" that reference by setting a bit in  */
/* the global "refbits" bitmap. */
/* This has to happen atomically, and has to happen atomically wrt GC. */
/* Note that updating a word in a bitmap is itself not atomic, unless we use */
/* interlocked loads and stores. */


/* For RPLACA and RPLACD, things are fairly simple: regardless of where we  */
/* are in the function, we can do the store (even if it's already been done)  */
/* and calculate whether or not we need to set the bit out-of-line.  (Actually */
/* setting the bit needs to be done atomically, unless we're sure that other */
/* threads are suspended.) */
/* We can unconditionally set the suspended thread's PC to its LR. */

        .globl C(egc_write_barrier_start)
        .globl C(egc_rplaca_did_store)
_spentry(rplaca)
C(egc_write_barrier_start):
        __(cmp arg_z,arg_y)
        __(_rplaca(arg_y,arg_z))
C(egc_rplaca_did_store):
        __(blo 9f)
        __(ref_global(temp0,ref_base))
        __(sub imm0,arg_y,temp0)
        __(lsr imm0,imm0,#dnode_shift)
        __(ref_global(imm1,oldspace_dnode_count))
        __(cmp imm0,imm1)
        __(bhs 9f)
        __(and imm2,imm0,#31)
        __(mov imm1,#0x80000000)
        __(lsr imm1,imm1,imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
0:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 0b)        
9:      __(ret)


        .globl C(egc_rplacd)
        .globl C(egc_rplacd_did_store)
_spentry(rplacd)
C(egc_rplacd):
        __(cmp arg_z,arg_y)
        __(_rplacd(arg_y,arg_z))
C(egc_rplacd_did_store):
        __(blo 9f)
        __(ref_global(temp0,ref_base))
        __(sub imm0,arg_y,temp0)
        __(lsr imm0,imm0,#dnode_shift)
        __(ref_global(imm1,oldspace_dnode_count))
        __(cmp imm0,imm1)
        __(bhs 9f)
        __(and imm2,imm0,#31)
        __(mov imm1,#0x80000000)
        __(lsr imm1,imm1,imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
0:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 0b)        
9:      __(ret)
	

/* Storing into a gvector can be handled the same way as storing into a CONS. */

	.globl C(egc_gvset)
        .globl C(egc_gvset_did_store)
_spentry(gvset)
C(egc_gvset):
        __(cmp arg_z,arg_x)
	__(lsl imm0,arg_y,#word_shift)
        /* Bug 156: check if gvset write hits frame + check frame integrity */
        __(add imm2,arg_x,imm0)
        __(and imm2,imm2,#0x00FFFFFFFFFFFFFF)
        __(sub imm2,imm2,x29)
        __(cmp imm2,#32)
        __(bhs 7f)
        __(hlt #0xFFF0)
7:      /* Also check frame integrity at gvset entry — check savefn directly */
        __(ldr imm2,[x29,#0x10])
        __(cbnz imm2,8f)
        __(hlt #0xFFEB)  /* savefn zeroed at gvset entry — new trap code with TCR info */
8:
	__(str arg_z,[arg_x,imm0])
C(egc_gvset_did_store):
        __(b.lo 9f)               
        __(add imm0,imm0,arg_x)
        __(ref_global(temp0,ref_base))
        __(sub imm0,imm0,temp0)
        __(lsr imm0,imm0,#dnode_shift)
        __(ref_global(imm1,oldspace_dnode_count))
        __(cmp imm0,imm1)
        __(bhs 9f)
        __(and imm2,imm0,#31)
        __(mov imm1,#0x80000000)
        __(lsr imm1,imm1,imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)	
0:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 0b)        
9:      __(ret)

        
/* This is a special case of storing into a gvector: if we need to memoize  */
/* the store, record the address of the hash-table vector in the refmap,  */
/* as well. */
        
        .globl C(egc_set_hash_key)
        .globl C(egc_set_hash_key_did_store)
_spentry(set_hash_key)
C(egc_set_hash_key):
        __(cmp arg_z,arg_x)
	__(lsl imm0,arg_y,#word_shift)
	__(str arg_z,[arg_x,imm0])
C(egc_set_hash_key_did_store):
        __(blo 9f)
        __(add imm0,imm0,arg_x)
        __(ref_global(temp0,ref_base))
        __(sub imm0,imm0,temp0)
        __(lsr imm0,imm0,#dnode_shift)
        __(ref_global(imm1,oldspace_dnode_count))
        __(cmp imm0,imm1)
        __(bhs 9f)
        __(and imm2,imm0,#31)
        __(mov imm1,#0x80000000)
        __(lsr imm1,imm1, imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
0:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 0b)        
/* Now need to ensure that the hash table itself is in the refmap; we
   know that it's in bounds, etc. */
        __(ref_global(temp0,ref_base))
        __(sub imm0,arg_x,temp0)
        __(lsr imm0,imm0, #dnode_shift)
        __(and imm2,imm0,#63)
        __(mov imm1,#0x8000000000000000)
        __(lsr imm1,imm1,imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
1:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 1b)        
9:      __(ret)
        

/*
   Interrupt handling (in pc_luser_xp()) notes: 
   If we are in this function and before the test which follows the
   conditional (at egc_store_node_conditional), or at that test
   and cr0`eq' is clear, pc_luser_xp() should just let this continue
   (we either haven't done the store conditional yet, or got a
   possibly transient failure.)  If we're at that test and the
   cr0`EQ' bit is set, then the conditional store succeeded and
   we have to atomically memoize the possible intergenerational
   reference.  Note that the local labels 4 and 5 are in the
   body of the next subprim (and at or beyond 'egc_write_barrier_end').

   N.B: it's not possible to really understand what's going on just
   by the state of the cr0`eq' bit.  A transient failure in the
   conditional stores that handle memoization might clear cr0`eq'
   without having completed the memoization.
*/

            .globl C(egc_store_node_conditional)
            .globl C(egc_write_barrier_end)
_spentry(store_node_conditional)
C(egc_store_node_conditional):
        __(vpop1(temp0))
         
1:      __(unbox_fixnum(imm2,temp0))
        __(add imm2,imm2,arg_x)
        __(ldxr temp1,[imm2])
        __(cmp temp1,arg_y)
        __(bne 5f)
        __(stxr gpr32(imm0),arg_z,[imm2])
        .globl C(egc_store_node_conditional_test)
C(egc_store_node_conditional_test): 
        __(cmp imm0,#0)
        __(bne 1b)
        __(cmp arg_z,arg_x)
        __(blo 4f)

        __(ref_global(imm0,ref_base))
        __(ref_global(imm1,oldspace_dnode_count))
        __(sub imm0,imm2,imm0)
        __(lsr imm0,imm0,#dnode_shift)
        __(cmp imm0,imm1)
        __(bhs 4f)
        __(and imm1,imm0,#31)
        __(mov arg_x,#0x80000000)
        __(lsr imm1,arg_x,imm1)
        __(ref_global(temp0,refbits))
        __(lsr imm0,imm0,#bitmap_shift)
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
2:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        .globl C(egc_set_hash_key_conditional_test)
C(egc_set_hash_key_conditional_test): 
        __(cmp imm0,#0)
        __(bne 2b)
        __(b 4f)
9:      __(ret)        
 
/* arg_z = new value, arg_y = expected old value, arg_x = hash-vector,
    vsp`0' = (boxed) byte-offset 
    Interrupt-related issues are as in store_node_conditional, but
    we have to do more work to actually do the memoization.*/
_spentry(set_hash_key_conditional)
        .globl C(egc_set_hash_key_conditional)
C(egc_set_hash_key_conditional):
        __(vpop1(imm1))
        __(unbox_fixnum(imm1,imm1))
0:      __(add imm2,arg_x,imm1)
        __(ldxr temp1,[imm2])
        __(cmp temp1,arg_y)
        __(bne 5f)
        __(stxr gpr32(imm0),arg_z,[imm2])
        __(cmp imm0,#0)
        __(bne 0b)
        .globl C(egc_set_hash_key_conditional_success)
C(egc_set_hash_key_conditional_success):
        __(cmp arg_z,arg_x)
        __(blo 4f)
        __(ref_global(temp0,ref_base))
        __(sub imm0,imm2,temp0)
        __(lsr imm0,imm0,#dnode_shift)
        __(ref_global(imm1,oldspace_dnode_count))
        __(cmp imm0,imm1)
        __(bhs 4f)
        __(and imm2,imm0,#31)
        __(mov imm1,#0x80000000)
        __(lsr imm1,imm1, imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
1:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 1b)        
/* Now need to ensure that the hash table itself is in the refmap; we
   know that it's in bounds, etc. */
        __(ref_global(temp0,ref_base))
        __(sub imm0,arg_x,temp0)
        __(lsr imm0,imm0,#dnode_shift)
        __(and imm2,imm0,#31)
        __(mov imm1,#0x80000000)
        __(lsr imm1,imm1,imm2)
        __(lsr imm0,imm0,#bitmap_shift)
        __(ref_global(temp0,refbits))
        __(add temp0,temp0,imm0,lsl #word_shift)
        __(ldr imm2,[temp0])
        __(tst imm2,imm1)
        __(bne 9f)
1:      __(ldxr imm2,[temp0])
        __(orr imm2,imm2,imm1)
        __(stxr gpr32(imm0),imm2,[temp0])
        __(cmp imm0,#0)
        __(bne 1b)        
C(egc_write_barrier_end):
4:      __(mov arg_z,rnil)
        __(add arg_z,arg_z,#t_offset)
        __(ret)
5:      __(_clrex(arg_z))
        __(mov arg_z,rnil)
9:      __(ret)




	
/* We always have to create a stack frame (even if nargs is 0), so the compiler  */
/* doesn't get confused.  */
_spentry(stkconslist)
        __(mov arg_z,rnil)
C(stkconslist_star):           
        __(lsl temp2,nargs,#1)
        __(dnode_align(temp2,temp2,node_size))
        __(mov imm1,#simple_vector_header<<tag_shift)
        __(add imm1,imm1,#1)
        __(add imm1,imm1,nargs,lsr #2)
        __(mov imm0,#tag_simple_vector)
        __(stack_allocate_zeroed_vector(imm0,imm1,temp2,imm0))
        __(add imm1,sp,#dnode_size+node_size)
        __(orr imm1,imm1,#tag_cons)
        __(cmp nargs,#0)
        __(b 4f)
1:      __(vpop1(temp0))
        __(_rplaca(imm1,temp0))
        __(_rplacd(imm1,arg_z))
        __(mov arg_z,imm1)
        __(add imm1,imm1,#cons.size)
        __(subs nargs,nargs,#node_size)
4:
        __(bne 1b)
        __(ret)

/* do list*: last arg in arg_z, all others vpushed,  */
/* nargs set to #args vpushed.  */
_spentry(stkconslist_star)
        __(b C(stkconslist_star))

/* Make a stack-consed simple-vector out of the NARGS objects  */
/* on top of the vstack; return it in arg_z.  */
_spentry(mkstackv)
        __(mov imm1,nargs)
        __(dnode_align(imm1,nargs,node_size))
        __(mov imm0,#simple_vector_header<<tag_shift)
        __(orr imm0,imm0,nargs,lsr #node_shift)
        __(mov imm2,#tag_simple_vector)
        __(stack_allocate_zeroed_vector(arg_z,imm0,imm1,imm2))
        __(add imm1,arg_z,nargs)
        __(b 4f)
3:      __(vpop1(arg_y))
        __(str arg_y,[imm1,#-node_size]!)
        __(sub nargs,nargs,#node_size)
4:      __(cbnz nargs,3b)
        __(ret)
	
_spentry(setqsym)
        __(ldr imm0,[arg_y,#symbol.flags])
        __(tst imm0,#sym_vbit_const_mask)
        __(beq _SPspecset)
        __(mov arg_z,arg_y)
        __(mov arg_y,#XCONST)
        __(set_nargs(2))
        __(b _SPksignalerr)



_spentry(progvsave)
        /* Error if arg_z isn't a proper list.  That's unlikely, */
        /* but it's better to check now than to crash later. */
        __(cmp arg_z,rnil)
        __(mov arg_x,arg_z) /* fast  */
        __(mov temp1,arg_z) /* slow  */
        __(beq 9f)  /* Null list is proper  */
0: 
        __(trap_unless_list(arg_x,imm0))
        __(_cdr(temp2,arg_x)) /* (null (cdr fast)) ?  */
        __(trap_unless_list(temp2,imm0))
        __(cmp temp2,rnil)
        __(_cdr(arg_x,temp2))
        __(beq 9f)
        __(_cdr(temp1,temp1))
        __(cmp arg_x,temp1)
        __(bne 0b)
        __(mov arg_y,#XIMPROPERLIST)
        __(set_nargs(2))
        __(b _SPksignalerr)
9:      /* Whew   */
 
        /* Next, determine the length of arg_y.  We  */
        /* know that it's a proper list.  */
        __(mov imm0,#0)
        __(mov arg_x,arg_y)
1:
        __(cmp arg_x,rnil)
        __(beq 2f)
        __(add imm0,imm0,#node_size)
        __(_cdr(arg_x,arg_x))
        __(b 1b)
2:
        /* imm0 is now (boxed) triplet count.  */
        /* Determine word count, add 1 (to align), and make room.  */
        /* if count is 0, make an empty tsp frame and exit  */
        __(cmp imm0,#0)
        __(add imm1,imm0,imm0,lsl #1)
        __(add imm1,imm1,#node_size) /* Room for binding count */
        __(dnode_align(imm2,imm1,node_size))
        __(bne 2f)
        __(make_header(imm0,1,simple_vector_header))
        __(mov imm1,#0)
        __(stp imm0,imm1,[sp,#-dnode_size]!)
        __(b 9f)
2:
        __(orr imm1,imm1,fixnumone) /* force odd */
        __(movk imm1,#(subtag_simple_vector << 8),lsl #48)
        __(mov temp1,sp)
        __(stack_allocate_zeroed_ivector(imm1,imm2))
        __(str imm0,[sp,#node_size])
        __(ldr imm1,[rcontext,#tcr.db_link])
3:      __(_car(temp0,arg_y))
        __(ldr imm0,[temp0,#symbol.binding_index])
        /* Bug 124: binding-index is already a byte offset */
        __(ldr imm2,[rcontext,#tcr.tlb_limit])
        __(_cdr(arg_y,arg_y))
        __(cmp imm2,imm0)
        __(bhi 4f)
        __(uuo_tlb_too_small(imm0))
4:              
        __(ldr arg_x,[rcontext,#tcr.tlb_pointer])
        __(ldr temp0,[arg_x,imm0])
        __(cmp arg_z,rnil)
        __(mov temp2,#unbound_marker)
        __(beq 5f)
        __(ldr temp2,[arg_z,#cons.car])
5:      __(_cdr(arg_z,arg_z))
        __(cmp arg_y,rnil)
        __(push1(temp0,temp1))
        __(push1(imm0,temp1))
        __(push1(imm1,temp1))
        __(mov imm1,temp1)
        __(str temp2,[arg_x,imm0])
        __(bne 3b)
        __(str imm1,[rcontext,#tcr.db_link])
9:              
        __(mov arg_z,#unbound_marker)
        __(mov imm2,#fixnum_one)
        __(mkcatch())        
        __(ret)
 
	
/* Allocate a uvector on the  stack.  (Push a frame on the stack and  */
/* heap-cons the object if there's no room on the stack.)  */
_spentry(stack_misc_alloc)
        /* Bug 156/157: if SP is above x29, stack allocation would overwrite the lisp frame.
           This can happen when NLX unwind restores SP to catch frame level.
           Fall through to heap allocation (SPmisc_alloc) which is safe.
           Bug 157: must move sp to x29 BEFORE pushing marker, otherwise the marker
           (tag_stack_alloc = 0x16) overwrites frame.savefn when sp = x29 + 32. */
        __(cmp sp,x29)
        __(bls 99f)
        __(mov imm1,sp)
        __(mov sp,x29)
        __(load_marker(imm0,tag_stack_alloc))
        __(stp imm0,imm1,[sp,#-dnode_size]!)
        __(b _SPmisc_alloc)
99:
        __(test_fixnum(imm0,arg_y))
        __(cbnz imm0,0f)
        __(branch_if_positive(arg_y,1f))
0:
        __(uuo_error_reg_not_xtype(arg_y,xtype_unsigned_byte_56))
1:
        /* arg_z = header subtag (e.g. 0x80=bignum, 0xA0+=gvector).
           arg_y = element count (raw fixnum, fixnumshift=0).
           Compute byte size in imm1 based on subtag element-size group.
           Subtag order: 32-bit(≤0x88) 64-bit(≤0x93) 8-bit(≤0x97) 16-bit(≤0x9B) 128-bit(0x9D) bit(0x9F) gvec(≥0xA0)
           Note: simple-base-string (0x87) is correctly in the 32-bit group
           because char-code-limit=#x110000 means 32-bit character elements. */
        __(cmp arg_z,#max_32_bit_ivector_subtag)
        __(lsl imm1,arg_y,#2)           /* 32-bit: count*4 */
        __(ble 8f)
        __(cmp arg_z,#max_64_bit_ivector_subtag)
        __(lsl imm1,arg_y,#3)           /* 64-bit: count*8 */
        __(ble 8f)
        __(cmp arg_z,#max_8_bit_ivector_subtag)
        __(mov imm1,arg_y)              /* 8-bit: count*1 */
        __(ble 8f)
        __(cmp arg_z,#max_16_bit_ivector_subtag)
        __(lsl imm1,arg_y,#1)           /* 16-bit: count*2 */
        __(ble 8f)
        __(cmp arg_z,#subtag_complex_double_float_vector)
        __(beq 6f)
        __(tst arg_z,#gvector_tag_mask)
        __(lsl imm1,arg_y,#3)           /* gvector: node-size (8 bytes) */
        __(bne 8f)
        /* bit-vector: count/8 rounded up */
        __(add imm1,arg_y,#7)
        __(lsr imm1,imm1,#3)
        __(b 8f)
6:      __(lsl imm1,arg_y,#4)           /* 128-bit: count*16 */
8:      __(dnode_align(imm1,imm1,node_size))
9:      
        __(ldr temp0,[rcontext,tcr.cs_limit])
        __(sub temp1,sp,imm1)
        __(cmp temp1,temp0)
        __(load_marker(temp0,tag_stack_alloc))
        __(mov temp1,sp)
        __(bls stack_misc_alloc_no_room)
        /* arg_z = header subtag (e.g. 0x80 for bignum).
           imm2 = reference tag = subtag ^ uvector_mask (e.g. 0x40).
           imm0 = header word: (subtag << subtag_shift) | element_count. */
        __(eor imm2,arg_z,#uvector_mask)
        __(lsl imm0,arg_z,#subtag_shift)
        __(orr imm0,imm0,arg_y)
        __(stack_allocate_zeroed_vector(arg_z,imm0,imm1,imm2))
        __(stp temp0,temp1,[sp,#-dnode_size]!)
        __(ret)
/* Too large to safely fit on stack.  Heap-cons the vector, but make  */
/* sure that there's an empty stack frame to keep the compiler happy.  */
stack_misc_alloc_no_room:       
        __(stp temp0,temp1,[sp,#-dnode_size]!)
        __(b _SPmisc_alloc)




/* subtype (boxed, of course) is vpushed, followed by nargs words worth of  */
/* initial-contents.  Note that this can be used to cons any type of initialized  */
/* node-header'ed misc object (symbols, closures, ...) as well as vector-like  */
/* objects.  */

_spentry(gvector)
        /* Bug 156: write entry marker to TCR.nfp to verify SPgvector is called */
        __(movz imm0,#0xCAFE)
        __(movk imm0,#0xBEEF,lsl #16)
        __(str imm0,[rcontext,#tcr.nfp])
        /* Bug 156: check frame integrity */
        __(ldr imm0,[x29,#0x08])
        __(cbnz imm0,0f)
        __(ldr imm0,[x29,#0x10])
        __(cbnz imm0,0f)
        __(hlt #0xFFF1)  /* frame zeroed by SPgvector time */
0:
        __(sub nargs,nargs,#node_size)
        __(ldr arg_z,[vsp,nargs])
        __(unbox_fixnum(imm0,arg_z))
        __(lsl imm0,imm0,#subtag_shift)
        __(orr imm0,imm0,nargs,lsr #node_shift)
        __(dnode_align(imm1,nargs,node_size))
        /* Bug 127: Derive correct TBI ref tag from subtag.
           arg_z still holds the raw subtag; compute ref_tag in temp0
           before Misc_Alloc overwrites arg_z with the result pointer. */
        __(eor temp0,arg_z,#0xC0)
        __(Misc_Alloc(arg_z,imm0,imm1,temp0))
        __(mov imm1,nargs)
        __(add imm2,imm1,#misc_data_offset)
        __(b 2f)
1:
        __(str temp0,[arg_z,imm2])
2:
        __(sub imm1,imm1,#node_size)
        __(cmp imm1,#0)
        __(sub imm2,imm2,#node_size)
        __(vpop1(temp0))        /* Note the intentional fencepost: */
                                /* discard the subtype as well.  */
        __(bge 1b)
        /* Bug 156: check frame integrity at SPgvector EXIT
           Check savefn DIRECTLY.
           Save savefn + x29 to GLOBAL variables for cross-check at SPgvset.
           (TCR fields get clobbered by exception handling.) */
        __(ldr imm0,[x29,#0x10])
        __(adrp imm1,_bug156_saved_savefn@PAGE)
        __(str imm0,[imm1,_bug156_saved_savefn@PAGEOFF])
        __(adrp imm1,_bug156_saved_x29@PAGE)
        __(str x29,[imm1,_bug156_saved_x29@PAGEOFF])
        __(cbnz imm0,3f)
        __(hlt #0xFFED)  /* savefn zeroed during SPgvector! */
3:
        __(ldr imm0,[x29,#0x08])
        __(cbnz imm0,4f)
        __(hlt #0xFFEC)  /* savelr zeroed during SPgvector! */
4:
        __(ret)

_spentry(fitvals)
        __(subs imm0,imm0,nargs)
        __(mov imm1,rnil)
        __(bge 2f)
        __(sub vsp,vsp,imm0)
        __(ret)
1:
        __(subs imm0,imm0,#node_size)
        __(vpush1(imm1))	
        __(add nargs,nargs,#node_size)
2:
        __(bne 1b)
0:      __(ret)


_spentry(nthvalue)
        __(add imm0,vsp,nargs)
        __(ldr imm1,[imm0,#0])
        __(cmp imm1,nargs) /*  do unsigned compare:  if (n < 0) => nil.  */
        __(mov arg_z,rnil)
        __(neg imm1,imm1)
        __(sub imm1,imm1,#node_size)
        __(bhs 1f)
        __(ldr arg_z,[imm0,imm1])
1:      __(add vsp,imm0,#node_size)
        __(ret)

/* Provide default (NIL) values for &optional arguments; imm0 is  */
/* the (fixnum) upper limit on the total of required and &optional  */
/* arguments.  nargs is preserved, all arguments wind up on the  */
/* vstack.  */
_spentry(default_optional_args)
        __(vpush_argregs())
        __(cmp nargs,imm0)
        __(mov arg_z,rnil)
        __(mov imm1,nargs)
        __(bhs 9f)
1: 
        __(add imm1,imm1,#node_size)
        __(cmp imm1,imm0)
        __(vpush1(arg_z))
        __(bne 1b)
9:      __(ret)

/* Indicate whether &optional arguments were actually supplied.  nargs  */
/* contains the actual arg count (minus the number of required args);  */
/* imm0 contains the number of &optional args in the lambda list.  */
/* Note that nargs may be > imm0 if &rest/&key is involved.  */
_spentry(opt_supplied_p)
        /* Bug 156: check caller's frame integrity on entry */
        __(ldr imm1,[x29,#0x10])
        __(cbnz imm1,0f)
        __(ldr imm1,[x29,#0x08])  /* also check savelr */
        __(cbnz imm1,0f)
        __(hlt #0xFFF4)  /* frame[savefn] AND frame[savelr] both 0 — frame never written */
0:
        __(mov imm1,#0)
        __(mov arg_x,rnil)
        __(add arg_x,arg_x,#t_offset)        
1:     
        /* (vpush (< imm1 nargs))  */
        __(cmp imm1,nargs)
        __(add imm1,imm1,#node_size)
        __(bne 2f)
        __(sub arg_x,arg_x,#t_offset)
2:      __(vpush1(arg_x))
        __(cmp imm1,imm0)
        __(bne 1b)
        __(ret)

/* Cons a list of length nargs  and vpush it.  */
/* Use this entry point to heap-cons a simple &rest arg.  */
_spentry(heap_rest_arg)
        __(vpush_argregs())
        __(mov imm1,nargs)
        __(mov arg_z,rnil)
        __(b 2f)
1:
        __(vpop1(arg_y))
        __(Cons(arg_z,arg_y,arg_z))
        __(subs imm1,imm1,#node_size)
2:
        __(cbnz imm1,1b)
        __(vpush1(arg_z))
        __(ret)


/* And this entry point when the argument registers haven't yet been  */
/* vpushed (as is typically the case when required/&rest but no  */
/* &optional/&key.)  */
_spentry(req_heap_rest_arg)
        __(vpush_argregs())
        __(subs imm1,nargs,imm0)
        __(mov arg_z,rnil)
        __(b 2f)
1:
        __(vpop1(arg_y))
        __(Cons(arg_z,arg_y,arg_z))
        __(subs imm1,imm1,#node_size)
2:
        __(bgt 1b)
        __(vpush1(arg_z))
        __(ret)

/* Here where argregs already pushed */
_spentry(heap_cons_rest_arg)
        __(subs imm1,nargs,imm0)
        __(mov arg_z,rnil)
        __(b 2f)
1:
        __(vpop1(arg_y))
        __(Cons(arg_z,arg_y,arg_z))
        __(subs imm1,imm1,#node_size)
2:
        __(bgt 1b)
        __(vpush1(arg_z))
        __(ret)



/* Check for pending FPU exceptions.
   Read FPSR, mask with enabled exceptions from TCR,
   signal error if any are set. */
_spentry(check_fpu_exception)
        __(mrs imm0,fpsr)
        __(mov imm2,imm0)
        __(ldr gpr32(imm1),[rcontext,#tcr.lisp_fpscr])
        __(and imm0,imm0,imm1,lsr #8)
        __(cbz imm0,0f)
        /* Clear exception flags in FPSR */
        __(bic imm2,imm2,#0xff)
        __(msr fpsr,imm2)
        __(build_lisp_frame())
        /* Allocate u64_vector[33] on stack: header(8) + 33*8 = 272 bytes */
        __(make_header(imm1,33,subtag_u64_vector))
        __(mov imm2,#272)
        __(stack_allocate_ivector(imm1,imm2))
        /* Tag stack pointer as misc object */
        __(add arg_z,sp,#node_size)
        __(orr arg_z,arg_z,#(fulltag_misc << tag_shift))
        /* Store exception flags at data[0] */
        __(str imm0,[arg_z,#misc_data_offset])
        /* Save all 32 double-precision FPU registers at data[1..32] */
        __(stp d0,d1,[sp,#16])
        __(stp d2,d3,[sp,#32])
        __(stp d4,d5,[sp,#48])
        __(stp d6,d7,[sp,#64])
        __(stp d8,d9,[sp,#80])
        __(stp d10,d11,[sp,#96])
        __(stp d12,d13,[sp,#112])
        __(stp d14,d15,[sp,#128])
        __(stp d16,d17,[sp,#144])
        __(stp d18,d19,[sp,#160])
        __(stp d20,d21,[sp,#176])
        __(stp d22,d23,[sp,#192])
        __(stp d24,d25,[sp,#208])
        __(stp d26,d27,[sp,#224])
        __(stp d28,d29,[sp,#240])
        __(stp d30,d31,[sp,#256])
        /* Load calling instruction for diagnostics */
        __(ldr gpr32(imm1),[lr,#-12])
        /* Signal FPU exception error */
        __(uuo_error_fpu_exception(arg_z,imm1))
        /* Continuation: restore FPU state */
        __(ldp d0,d1,[sp,#16])
        __(ldp d2,d3,[sp,#32])
        __(ldp d4,d5,[sp,#48])
        __(ldp d6,d7,[sp,#64])
        __(ldp d8,d9,[sp,#80])
        __(ldp d10,d11,[sp,#96])
        __(ldp d12,d13,[sp,#112])
        __(ldp d14,d15,[sp,#128])
        __(ldp d16,d17,[sp,#144])
        __(ldp d18,d19,[sp,#160])
        __(ldp d20,d21,[sp,#176])
        __(ldp d22,d23,[sp,#192])
        __(ldp d24,d25,[sp,#208])
        __(ldp d26,d27,[sp,#224])
        __(ldp d28,d29,[sp,#240])
        __(ldp d30,d31,[sp,#256])
        /* Deallocate vector and return */
        __(add sp,sp,#272)
        __(return_lisp_frame())
0:
        __(ret)
_endsubp(check_fpu_exception)


_spentry(discard_stack_object)
        new_local_labels()
        __(ldr imm0,[sp,#0])
        /* Check for stack_alloc_marker by tag byte */
        __(lsr imm1,imm0,#tag_shift)
        __(cmp imm1,#tag_stack_alloc)
        __(bne 1f)
        __(ldr imm0,[sp,#node_size])
        __(mov sp,imm0)
        __(b 9f)
1:      /* Check for lisp_frame_marker by tag byte */
        __(cmp imm1,#tag_lisp_frame)
        __(bne 2f)
        __(add sp,sp,#lisp_frame.size)
        __(b 9f)
2:      /* Must be a header.  Check if ivector (immheader) */
        /* Bug 160/161: imm1 already has the top byte (subtag) from the
           tag_shift extraction above.  Check uvector_header bit in the
           subtag byte, NOT in the raw 64-bit value (which has the count
           in the low bits, not the subtag).
           Bug 161: Classification must match SPstack_misc_alloc.
           Subtag order on ARM64: 32-bit(<=0x88) 64-bit(<=0x93) 8-bit(<=0x97)
           16-bit(<=0x9B) 128-bit(0x9D) bit(0x9F) gvec(>=0xA0).
           Previous code missed the 64-bit case, so macptr/s64/u64 etc.
           were misclassified as 8-bit, computing wrong skip size. */
        __(tst imm1,#uvector_header)
        __(beq 9f)
        /* imm1 still has the subtag from the earlier lsr */
        __(ubfx imm0,imm0,#0,#subtag_shift)
        __(tst imm1,#gvector_tag_mask)
        __(beq local_label(ivector))
local_label(gvec):
        /* gvector: count * node_size (8 bytes per element) */
        __(lsl imm0,imm0,#word_shift)
local_label(out):
        __(dnode_align(imm0,imm0,node_size))
        __(add sp,sp,imm0)
9:      __(ret)
local_label(ivector):
        __(cmp imm1,#max_32_bit_ivector_subtag)
        __(bls local_label(word32))
        __(cmp imm1,#max_64_bit_ivector_subtag)
        __(bls local_label(gvec))       /* 64-bit: count*8, same as gvector */
        __(cmp imm1,#max_8_bit_ivector_subtag)
        __(bhi 3f)
        __(b local_label(out))          /* 8-bit: count*1 */
3:      __(cmp imm1,#max_16_bit_ivector_subtag)
        __(bhi 4f)
        __(lsl imm0,imm0,#1)           /* 16-bit: count*2 */
        __(b local_label(out))
4:      __(cmp imm1,#subtag_bit_vector)
        __(bne 5f)
        __(add imm0,imm0,#7)           /* bit: (count+7)/8 */
        __(lsr imm0,imm0,#3)
        __(b local_label(out))
5:      /* 128-bit: complex-double-float-vector, count*16 */
        __(lsl imm0,imm0,#dnode_shift)
        __(b local_label(out))
local_label(word32):
        /* 32-bit ivectors: count*4 */
        __(lsl imm0,imm0,#2)
        __(b local_label(out))

	
/* Signal an error synchronously, via %ERR-DISP.  */
/* If %ERR-DISP isn't fbound, it'd be nice to print a message  */
/* on the C runtime stderr.  */
 
_spentry(ksignalerr)
        __(ref_nrs_symbol(fname,errdisp))
        __(jump_fname)

/* As in the heap-consed cases, only stack-cons the &rest arg  */
_spentry(stack_rest_arg)
        __(mov imm0,#0)
        __(vpush_argregs())
        __(b _SPstack_cons_rest_arg)

_spentry(req_stack_rest_arg)
        __(vpush_argregs())
        __(b _SPstack_cons_rest_arg)

_spentry(stack_cons_rest_arg)
        __(subs imm1,nargs,imm0)
        __(mov arg_z,rnil)
        __(ble 2f)  /* always temp-push something.  */
        __(mov temp0,imm1)
        __(add imm1,imm1,imm1)
        __(add imm1,imm1,#node_size)
        __(dnode_align(imm0,imm1,node_size))
        __(movk imm1,#(subtag_u64_vector << 8),lsl #48)
        __(sub arg_x,sp,imm0)
        __(ldr arg_y,[rcontext,#tcr.cs_limit])
        __(cmp arg_x,arg_y)
        __(blo 3f)
        __(stack_allocate_zeroed_ivector(imm1,imm0))
        __(mov imm0,#subtag_simple_vector)
        __(strb gpr32(imm0),[sp,#7])
        __(add imm0,sp,#dnode_size)
        __(orr imm0,imm0,#(fulltag_cons << tag_shift))
1:
        __(subs temp0,temp0,#node_size)
        __(vpop1(arg_x))
        __(_rplacd(imm0,arg_z))
        __(_rplaca(imm0,arg_x))
        __(mov arg_z,imm0)
        __(add imm0,imm0,#cons.size)
        __(bne 1b)
        __(vpush1(arg_z))
        __(ret)
2:
        __(make_header(imm0,1,subtag_u64_vector))
        __(mov imm1,#0)
        __(stp imm0,imm1,[sp,#-dnode_size]!)
        __(vpush1(arg_z))
        __(ret)
3:
        __(load_marker(arg_z,tag_stack_alloc))
        __(mov arg_y,sp)
        __(stp arg_z,arg_y,[sp,#-dnode_size]!)
        __(b _SPheap_cons_rest_arg)

	
/* Prepend all but the first three (entrypoint, closure code, fn) and last two  */
/* (function name, lfbits) elements of nfn to the "arglist".  */
/* functions which take "inherited arguments" work consistently  */
/* even in cases where no closure object is created.  */
_spentry(call_closure)
        __(cmp nargs,#nargregs*node_size)
        __(vector_length(imm0,nfn,imm0))
        /* imm0 = raw element count.  Scale to nargs units (node_size). */
        __(lsl imm0,imm0,#node_shift)
        __(sub imm0,imm0,#5*node_size) /* imm0 = inherited arg count (scaled)  */
        __(ble local_label(no_insert))
        /* Some arguments have already been vpushed.  Vpush imm0's worth  */
        /* of NILs, copy those arguments that have already been vpushed from  */
        /* the old TOS to the new, then insert all of the inerited args  */
        /* and go to the function.  */
        __(vpush_all_argregs())
        __(mov arg_x,imm0)
        __(mov arg_y,rnil)
local_label(push_nil_loop):
        __(subs arg_x,arg_x,#node_size)
        __(vpush1(arg_y))
        __(bne local_label(push_nil_loop))
        __(add arg_y,vsp,imm0)
        __(mov imm1,#0)
local_label(copy_already_loop):
        __(ldr arg_x,[arg_y,imm1])
        __(str arg_x,[vsp,imm1])
        __(add imm1,imm1,#node_size)
        __(cmp imm1,nargs)
        __(bne local_label(copy_already_loop))
        __(mov imm1,#misc_data_offset+(3*node_size))
        __(add arg_y,vsp,nargs)
        __(add arg_y,arg_y,imm0)
local_label(insert_loop):
        __(subs imm0,imm0,#node_size)
        __(ldr fname,[nfn,imm1])
        __(add imm1,imm1,#node_size)
        __(add nargs,nargs,#node_size)
        __(push1(fname,arg_y))
        __(bne local_label(insert_loop))
        __(vpop_all_argregs())
        __(b local_label(go))
local_label(no_insert):
/* nargregs or fewer args were already vpushed.  */
/* if exactly nargregs, vpush remaining inherited vars.  */
        __(cmp nargs,#nargregs*node_size)
        __(add imm1,imm0,#misc_data_offset+(3*node_size))
        __(bne local_label(set_regs))
local_label(vpush_remaining):
        __(mov imm1,#misc_data_offset+(3*node_size))
local_label(vpush_remaining_loop):
        __(ldr fname,[nfn,imm1])
        __(add imm1,imm1,#node_size)
        __(vpush1(fname))
        __(subs imm0,imm0,#node_size)
        __(add nargs,nargs,#node_size)
        __(bne  local_label(vpush_remaining_loop))
        __(b local_label(go))
local_label(set_regs):
        /* if nargs was > 1 (and we know that it was < 3), it must have  */
        /* been 2.  Set arg_x, then vpush the remaining args.  */
        __(cmp nargs,#node_size)
        __(ble local_label(set_y_z))
local_label(set_arg_x):
        __(subs imm0,imm0,#node_size)
        __(sub imm1,imm1,#node_size)
        __(ldr arg_x,[nfn,imm1])
        __(add nargs,nargs,#node_size)
        __(bne local_label(vpush_remaining))
        __(b local_label(go))
        /* Maybe set arg_y or arg_z, preceding args  */
local_label(set_y_z):
        __(cmp nargs,#node_size)
        __(bne local_label(set_arg_z))
        /* Set arg_y, maybe arg_x, preceding args  */
local_label(set_arg_y):
        __(subs imm0,imm0,#node_size)
        __(sub imm1,imm1,#node_size)
        __(ldr arg_y,[nfn,imm1])
        __(add nargs,nargs,#node_size)
        __(bne local_label(set_arg_x))
        __(b local_label(go))
local_label(set_arg_z):
        __(subs imm0,imm0,#node_size)
        __(sub imm1,imm1,#node_size)
        __(ldr arg_z,[nfn,imm1])
        __(add nargs,nargs,#node_size)
        __(bne local_label(set_arg_y))
 
local_label(go):
        __(vrefr(nfn,nfn,2))
        __(jump_nfn())


/* Everything up to the last arg has been vpushed, nargs is set to  */
/* the (boxed) count of things already pushed.  */
/* On exit, arg_x, arg_y, arg_z, and nargs are set as per a normal  */
/* function call (this may require vpopping a few things.)  */
/* ppc2-invoke-fn assumes that temp1 is preserved here.  */
_spentry(spreadargz)
        __(extract_lisptag(imm1,arg_z))
        __(cmp arg_z,rnil) 
        __(mov imm0,#0)
        __(mov arg_y,arg_z)  /*  save in case of error  */
        __(beq 2f)
1:
        __(cmp imm1,#tag_list)
        __(bne 3f)
        __(_car(arg_x,arg_z))
        __(_cdr(arg_z,arg_z))
        __(cmp arg_z,rnil)
        __(extract_lisptag(imm1,arg_z))
        __(vpush1(arg_x))
        __(add imm0,imm0,#node_size)
        __(bne 1b)
2:
        __(add  nargs,nargs,imm0)
        __(vpop_argregs())
        __(ret)
	
        /*  Discard whatever's been vpushed already, complain.  */
3: 
        __(add vsp,vsp,imm0)
        __(mov arg_z,arg_y)  /* recover original arg_z  */
        __(mov arg_y,#XNOSPREAD)
        __(set_nargs(2))
        __(b _SPksignalerr)

/* Tail-recursively funcall temp0.  */
/* Pretty much the same as the tcallsym* cases above.  */
/* Bug 158 fix: restore x29 from frame before discarding it.  */
_spentry(tfuncallgen)
        __(cmp nargs,#nargregs*node_size)
        __(ldr lr,[sp,#lisp_frame.savelr])
        __(ble 2f)
        __(ldr imm0,[sp,#lisp_frame.savevsp])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        /* can use temp0 as a temporary  */
        __(sub imm1,nargs,#nargregs*node_size)
        __(add imm1,imm1,vsp)
1:
        __(ldr temp0,[imm1,#-node_size]!)
        __(cmp imm1,vsp)
        __(push1(temp0,imm0))
        __(bne 1b)
        __(mov vsp,imm0)
        __(funcall_nfn())
2:
        __(ldr vsp,[sp,#lisp_frame.savevsp])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        __(funcall_nfn())


/* Some args were vpushed.  Slide them down to the base of  */
/* the current frame, then do funcall.  */
_spentry(tfuncallslide)
        __(ldr imm0,[sp,#lisp_frame.savevsp])
        __(ldr lr,[sp,#lisp_frame.savelr])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        /* can use temp0 as a temporary  */
        __(sub imm1,nargs,#nargregs*node_size)
        __(add imm1,imm1,vsp)
1:
        __(ldr temp0,[imm1,#-node_size]!)
        __(cmp imm1,vsp)
        __(push1(temp0,imm0))
        __(bne 1b)
        __(mov vsp,imm0)
        __(funcall_nfn())


_spentry(jmpsym)
        __(jump_fname)

/* Tail-recursively call the (known symbol) in fname.  */
/* In the general case, we don't know if any args were  */
/* vpushed or not.  If so, we have to "slide" them down  */
/* to the base of the frame.  If not, we can just restore  */
/* vsp, lr, fn from the saved lisp frame on the control stack.  */
/* Bug 158 fix: restore x29 from frame before discarding in all tail-call subprims. */
_spentry(tcallsymgen)
        __(cmp nargs,#nargregs*node_size)
        __(ldr lr,[sp,#lisp_frame.savelr])
        __(ble 2f)

        __(ldr imm0,[sp,#lisp_frame.savevsp])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        /* can use nfn (= temp2) as a temporary  */
        __(sub imm1,nargs,#nargregs*node_size)
        __(add imm1,imm1,vsp)
1:
        __(ldr temp2,[imm1,#-node_size]!)
        __(cmp imm1,vsp)
        __(push1(temp2,imm0))
        __(bne 1b)
        __(mov vsp,imm0)
        __(jump_fname)

2:
        __(ldr vsp,[sp,#lisp_frame.savevsp])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        __(jump_fname)


/* Some args were vpushed.  Slide them down to the base of  */
/* the current frame, then do funcall.  */
_spentry(tcallsymslide)
        __(ldr lr,[sp,#lisp_frame.savelr])
        __(ldr imm0,[sp,#lisp_frame.savevsp])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        /* can use nfn (= temp2) as a temporary  */
        __(sub imm1,nargs,#nargregs*node_size)
        __(add imm1,imm1,vsp)
1:
        __(ldr temp2,[imm1,#-node_size]!)
        __(cmp imm1,vsp)
        __(push1(temp2,imm0))
        __(bne 1b)
        __(mov vsp,imm0)
        __(jump_fname)


/* Tail-recursively call the function in nfn.  */
/* Bug 158 fix: on ARM64 fn=nfn=x10, so restore_lisp_frame() clobbers the
   callee in nfn.  Instead, restore only x29/vsp/lr and leave nfn alone. */
_spentry(tcallnfngen)
        __(cmp nargs,#nargregs*node_size)
        __(bgt _SPtcallnfnslide)
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(ldp vsp,lr,[sp],#lisp_frame.size)
        __(jump_nfn())

/* Some args were vpushed.  Slide them down to the base of  */
/* the current frame, then do funcall.  */
_spentry(tcallnfnslide)
        __(ldr lr,[sp,#lisp_frame.savelr])
        __(ldr imm0,[sp,#lisp_frame.savevsp])
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(discard_lisp_frame())
        /* Since we have a known function, can use fname as a temporary.  */
        __(sub imm1,nargs,#nargregs*node_size)
        __(add imm1,imm1,vsp)
1:
        __(ldr fname,[imm1,#-node_size]!)
        __(cmp imm1,vsp)
        __(push1(fname,imm0))
        __(bne 1b)
        __(mov vsp,imm0)
        __(jump_nfn())


/* Reference index arg_z of a misc-tagged object (arg_y).  */
/* Note that this conses in some cases.  Return a properly-tagged  */
/* lisp object in arg_z.  Do type and bounds-checking.  */

_spentry(misc_ref)
        __(extract_tag(imm1,arg_y))
        __(and imm0,imm1,#uvector_mask)
        __(cmp imm0,#uvector_ref)
        __(beq 0f)
        __(uuo_error_reg_not_xtype(arg_y,xtype_uvector))
0:              
        __(vector_length(imm0,arg_y,imm1))
        __(cmp arg_z,imm0)
        __(blo 1f)
        __(trap_unless_fixnum(arg_z,imm1))
        __(uuo_error_vector_bounds(arg_z,arg_y))
1:
        __(extract_lowbyte(imm1,imm1))
        __(b C(misc_ref_common))

/* like misc_ref, only the boxed subtag is in arg_x.  */

_spentry(subtag_misc_ref)
        __(trap_unless_fulltag_equal(arg_y,fulltag_misc,imm0))
        __(trap_unless_fixnum(arg_z))
        __(vector_length(imm0,arg_y,imm1))
        __(cmp arg_z,imm0)
        __(blo 1f)
        __(uuo_error_vector_bounds(arg_z,arg_y))
1:              
        __(unbox_fixnum(imm1,arg_x))
        __(b C(misc_ref_common))


/* Make a "raw" area on the temp stack, stack-cons a macptr to point to it,  */
/* and return the macptr.  Size (in bytes, boxed) is in arg_z on entry; macptr */
/* in arg_z on exit.  */
_spentry(makestackblock)
        /* Bug 156/157: if SP > x29, stack alloc would corrupt the frame.
           Redirect to heap allocation path (same as "too big" case).
           Bug 157: move sp to x29 before pushing marker to avoid
           overwriting frame.savefn with tag_stack_alloc. */
        __(cmp sp,x29)
        __(bls 0f)
        __(mov temp0,sp)
        __(mov sp,x29)
        __(load_marker(imm1,tag_stack_alloc))
        __(stp imm1,temp0,[sp,#-dnode_size]!)
        __(set_nargs(1))
        __(ref_nrs_symbol(fname,new_gcable_ptr))
        __(jump_fname())
0:
        __(unbox_fixnum(imm1,arg_z))
        __(dnode_align(imm1,imm1,0))
        __(add imm1,imm1,#node_size)
        __(add imm0,imm1,#node_size)
        __(sub imm2,sp,imm0)
        __(ldr temp0,[rcontext,#tcr.cs_limit])
        __(cmp imm2,temp0)
        __(mov temp0,sp)
        __(bls 1f)
        __(movk imm1,#(subtag_u8_vector << 8),lsl #48)
        __(stack_allocate_ivector(imm1,imm0))
        __(add temp1,sp,#dnode_size)
        __(make_header(imm1,macptr.element_count,subtag_macptr))
        __(str imm1,[sp,#-macptr.size]!)
        __(add arg_z,sp,#node_size)
        __(orr arg_z,arg_z,#(fulltag_misc << tag_shift))
        __(str temp1,[arg_z,#macptr.address])
        __(mov imm0,#0)
        __(load_marker(imm1,tag_stack_alloc))
        __(str imm0,[arg_z,#macptr.type])
        __(str imm0,[arg_z,#macptr.domain])
        __(stp imm1,temp0,[sp,#-dnode_size]!)
        __(ret)

        /* Too big. Heap cons a gcable macptr  */
1:
        __(load_marker(imm1,tag_stack_alloc))
        __(stp imm1,temp0,[sp,#-dnode_size]!)
        __(set_nargs(1))
        __(ref_nrs_symbol(fname,new_gcable_ptr))
        __(jump_fname())

/* As above, only set the block's contents to 0.  */
_spentry(makestackblock0)
        __(unbox_fixnum(imm1,arg_z))
        __(dnode_align(imm1,imm1,0))
        __(add imm1,imm1,#node_size)
        __(add imm0,imm1,#node_size)
        __(sub imm2,sp,imm0)
        __(ldr temp0,[rcontext,#tcr.cs_limit])
        __(cmp imm2,temp0)
        __(mov temp0,sp)
        __(bls 1f)
        __(movk imm1,#(subtag_u8_vector << 8),lsl #48)
        __(stack_allocate_zeroed_ivector(imm1,imm0))
        __(add temp1,sp,#dnode_size)
        __(make_header(imm1,macptr.element_count,subtag_macptr))
        __(str imm1,[sp,#-macptr.size]!)
        __(add arg_z,sp,#node_size)
        __(orr arg_z,arg_z,#(fulltag_misc << tag_shift))
        __(str temp1,[arg_z,#macptr.address])
        __(mov imm0,#0)
        __(load_marker(imm1,tag_stack_alloc))
        __(str imm0,[arg_z,#macptr.type])
        __(str imm0,[arg_z,#macptr.domain])
        __(stp imm1,temp0,[sp,#-dnode_size]!)
        __(ret)

        /* Too big. Heap cons a gcable macptr  */
1:
        __(load_marker(imm1,tag_stack_alloc))
        __(stp imm1,temp0,[sp,#-dnode_size]!)
        __(mov arg_y,arg_z) /* save block size  */
        __(mov arg_z,rnil) /* clear-p arg to %new-gcable-ptr  */
        __(add arg_z,arg_z,#t_offset)
        __(set_nargs(2))
        __(ref_nrs_symbol(fname,new_gcable_ptr))
        __(jump_fname())

/* Make a list of length arg_y (boxed), initial-element arg_z (boxed) on  */
/* the tstack.  Return the list in arg_z.  */
_spentry(makestacklist)
        __(add imm0,arg_y,arg_y)
        __(add imm1,imm0,#1)
        __(movk imm1,#(subtag_u64_vector << 8),lsl #48)
        __(add imm0,imm0,#dnode_size)
        __(ldr temp0,[rcontext,#tcr.cs_limit])
        __(sub imm2,sp,imm0)
        __(cmp imm2,temp0)
        __(bls 4f)
        __(stack_allocate_zeroed_ivector(imm1,imm0))
        __(mov imm0,#subtag_simple_vector)
        __(strb gpr32(imm0),[sp,#7])
        __(add imm2,sp,#dnode_size)
        __(orr imm2,imm2,#(fulltag_cons << tag_shift))
        __(mov imm1,arg_y)
        __(mov arg_y,arg_z)
        __(mov arg_z,rnil)
        __(b 3f)
2:
        __(_rplacd(imm2,arg_z))
        __(_rplaca(imm2,arg_y))
        __(mov arg_z,imm2)
        __(add imm2,imm2,#cons.size)
        __(sub imm1,imm1,#fixnumone)
3:
        __(cbnz imm1,2b)
        __(ret)
4:
        __(make_header(imm0,1,subtag_u64_vector))
        __(str imm0,[sp,#-dnode_size]!)
        __(mov imm1,arg_y) /* count  */
        __(mov arg_y,arg_z) /* initial value  */
        __(mov arg_z,rnil) /* result  */
        __(b 6f)
5:
        __(Cons(arg_z,arg_y,arg_z))
        __(sub imm1,imm1,#fixnumone)
6:
        __(cbnz imm1,5b)
        __(ret)

/* subtype (boxed) vpushed before initial values. (Had better be a  */
/* node header subtag.) Nargs set to count of things vpushed.  */

_spentry(stkgvector)
        /* Bug 156: check frame integrity */
        __(ldr imm0,[x29,#0x08])
        __(cbnz imm0,0f)
        __(ldr imm0,[x29,#0x10])
        __(cbnz imm0,0f)
        __(hlt #0xFFF3)  /* frame zeroed by SPstkgvector time */
0:
        __(sub imm0,nargs,#node_size)
        __(ldr temp0,[vsp,imm0])
        __(dnode_align(temp1,imm0,node_size))
        __(mov imm1,imm0)
        __(movk imm1,#(subtag_u64_vector << 8),lsl #48)
        __(sub temp2,sp,imm1)
        __(ldr arg_x,[rcontext,#tcr.cs_limit])
        __(cmp temp2,arg_x)       
        __(mov temp2,sp)
        __(load_marker(arg_x,tag_stack_alloc))
        __(bls 3f)
        /* Bug 156: check sp <= x29 before zeroing */
        __(cmp sp,x29)
        __(bls 4f)
        __(hlt #0xFFF5)
4:
        __(stack_allocate_zeroed_ivector(imm1,temp1))
        __(unbox_fixnum(imm1,temp0))
        __(strb gpr32(imm1),[sp,#7])
        __(add arg_z,sp,#node_size)
        __(orr arg_z,arg_z,#(fulltag_misc << tag_shift))
        __(add imm0,sp,nargs)
        __(stp arg_x,temp2,[sp,#-dnode_size]!)
        __(b 2f)
1:
        __(vpop1(temp0))
        __(push1(temp0,imm0))
2:      __(subs nargs,nargs,#node_size)
        __(bne 1b)
        __(add vsp,vsp,#node_size)
        __(ret)
3:      /* Have to heap-cons. */
        __(stp arg_x,temp2,[sp,#-dnode_size]!)
        __(vpush1(nargs))
        __(mov arg_y,nargs)
        __(mov arg_z,temp0)
        __(build_lisp_frame())
        __(bl _SPmisc_alloc)
        __(restore_lisp_frame())
        __(vpop1(nargs))
        __(add imm0,nargs,#misc_data_offset)
        __(b 5f)
4:      __(vpop1(temp0))
        __(subs imm0,imm0,#node_size)
        __(str temp0,[arg_z,imm0])
5:      __(subs nargs,nargs,#node_size)
        __(bne 4b)
        __(add vsp,vsp,#node_size)
        __(ret)
        
/* Allocate a "fulltag_misc" object.  On entry, arg_y contains the element  */
/* count (boxed) and  arg_z contains the subtag (boxed).  Both of these   */
/* parameters must be "reasonable" (the  subtag must be valid, the element  */
/* count must be of type (unsigned-byte 24)/(unsigned-byte 56).   */
/* On exit, arg_z contains the (properly tagged) misc object; it'll have a  */
/* proper header on it and its contents will be 0.   imm0 contains   */
/* the object's header (fulltag = fulltag_immheader or fulltag_nodeheader.)  */

/* arg_y = element count (fixnum, fixnumshift=0 so raw integer).
   arg_z = subtag (fixnum).
   Allocate a misc object on the heap.
   ARM64 fixnumshift=0: arg_y IS the element count directly, so we must
   explicitly scale to byte count for each element-size group. */
_spentry(misc_alloc)
        __(tst arg_y,#unsigned_byte_24_mask)
        __(bne 9f)
        __(unbox_fixnum(imm0,arg_z))
        __(lsl imm0,imm0,#subtag_shift)
        __(orr imm0,imm0,arg_y)         /* imm0 = header: (subtag << 56) | count */
        __(lsr imm1,imm0,#subtag_shift)  /* imm1 = subtag */
        __(tst imm1,#gvector_tag_mask)
        __(lsl imm2,arg_y,#3)           /* gvector: count * 8 (node-size) */
        __(bne 1f)
        /* ivector size dispatch — subtag order:
           32-bit(≤0x88) 64-bit(≤0x93) 8-bit(≤0x97) 16-bit(≤0x9B) 128-bit(0x9D) bit(0x9F) */
        __(cmp imm1,#max_32_bit_ivector_subtag)
        __(lsl imm2,arg_y,#2)           /* 32-bit: count * 4 */
        __(ble 1f)
        __(cmp imm1,#max_64_bit_ivector_subtag)
        __(lsl imm2,arg_y,#3)           /* 64-bit: count * 8 */
        __(ble 1f)
        __(cmp imm1,#max_8_bit_ivector_subtag)
        __(mov imm2,arg_y)              /* 8-bit: count * 1 */
        __(ble 1f)
        __(cmp imm1,#max_16_bit_ivector_subtag)
        __(lsl imm2,arg_y,#1)           /* 16-bit: count * 2 */
        __(ble 1f)
        __(cmp imm1,#subtag_complex_double_float_vector)
        __(beq 6f)
        /* bit-vector: (count + 7) / 8 */
        __(add imm2,arg_y,#7)
        __(lsr imm2,imm2,#3)
        __(b 1f)
6:      __(lsl imm2,arg_y,#4)           /* 128-bit: count * 16 */
1:
        __(dnode_align(imm2,imm2,node_size))
        /* Bug 127: Derive correct TBI ref tag from header subtag.
           imm1 still holds the subtag (set at line above).
           ref_tag = subtag XOR 0xC0 (converts header bit to ref bit). */
        __(eor imm1,imm1,#0xC0)
        __(Misc_Alloc(arg_z,imm0,imm2,imm1))
        __(ret)
9:
        __(uuo_error_reg_not_xtype(arg_y,xtype_unsigned_byte_24))



_spentry(atomic_incf_node)
        __(build_lisp_frame())
        __(add lr,arg_y,arg_z,asr #fixnumshift)
0:      __(ldxr arg_z,[lr])
        __(add arg_z,arg_z,arg_x)
        __(stxr gpr32(imm0),arg_z,[lr])
        __(cmp imm0,#0)
        __(bne 0b)
       /* Return this way, to get something else in the lr */
        __(restore_lisp_frame())
        __(ret)
        
_spentry(unused1)

_spentry(unused2)

/* vpush the values in the value set atop the stack, incrementing nargs.  */

define(`mvcall_older_value_set',`node_size')
define(`mvcall_younger_value_set',`node_size+4')
        

_spentry(recover_values)
        __(add temp0,sp,#dnode_size)
        /* Find the oldest set of values by walking links from the newest */
0:              
        __(ldr temp1,[temp0,#mvcall_older_value_set])
        __(cbz temp1,1f)
        __(mov temp0,temp1)
        __(b 0b)
1:      __(ldr imm0,[temp0])
        __(header_length(imm0,imm0))
        __(subs imm0,imm0,#2<<fixnumshift)
        __(add temp1,temp0,#node_size+8)
        __(add temp1,temp1,imm0)
        __(b 3f)
2:      __(subs imm0,imm0,#fixnumone)        
        __(ldr arg_z,[temp1,#-node_size]!)
        __(vpush1(arg_z))
        __(add nargs,nargs,#node_size)
3:      __(bne 2b)
        __(ldr temp0,[temp0,#mvcall_younger_value_set])
        __(cmp temp0,#0)
        __(bne 1b)
        __(ldr imm0,[sp,#node_size])
        __(mov sp,imm0)
        __(ret)


/* If arg_z is an integer, return in imm0 something whose sign  */
/* is the same as arg_z's.  If not an integer, error.  */
/* Bug 161: Same clobbering issue as SPgets64. branch_if_fixnum uses imm0
   as scratch, clobbering the value. Fix: test first, then mov. */
_spentry(integer_sign)
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(mov imm0,arg_z)
        __(b 9f)
1:      __(extract_typecode(imm0,arg_z))
        __(cmp imm0,#subtag_bignum)
        __(beq 1f)
        __(uuo_error_reg_not_xtype(arg_z,xtype_integer))
1:              
        __(getvheader(imm1,arg_z))
        __(header_length(imm0,imm1)) /* boxed length = scaled size  */
        __(add imm0,imm0,#misc_data_offset-4) /* bias, less 1 element  */
        __(ldr imm0,[arg_z,imm0])
9:      __(ret)


/* like misc_set, only pass the (boxed) subtag in temp0  */
_spentry(subtag_misc_set)
        __(trap_unless_fulltag_equal(arg_x,fulltag_misc,imm0))
        __(trap_unless_fixnum(arg_y))
        __(vector_length(imm0,arg_x,imm1))
        __(cmp arg_y,imm0)
        __(blo 1f)
        __(uuo_error_vector_bounds(arg_y,arg_x))
1:              
        __(unbox_fixnum(imm1,temp0))
        __(b C(misc_set_common))



/* misc_set (vector index newval).  Pretty damned similar to  */
/* misc_ref, as one might imagine.  */

_spentry(misc_set)
        __(trap_unless_fulltag_equal(arg_x,fulltag_misc,imm0))
        __(trap_unless_fixnum(arg_y))
        __(vector_length(imm0,arg_x,imm1))
        __(cmp arg_y,imm0)
        __(blo 1f)
        __(uuo_error_vector_bounds(arg_y,arg_x))
1:              
        __(extract_lowbyte(imm1,imm1))
        __(b C(misc_set_common))

/* "spread" the lexpr in arg_z.  */
/* ppc2-invoke-fn assumes that temp1 is preserved here.  */
_spentry(spread_lexprz)
        __(ldr imm0,[arg_z,#0])
        __(add imm1,arg_z,imm0,lsl #node_shift)
        __(add nargs,nargs,imm0,lsl #node_shift)
        __(add imm1,imm1,#node_size)
        __(cmp imm0,#3<<fixnumshift)
        __(bge 9f)
        __(cmp imm0,#2<<fixnumshift)
        __(beq 2f)
        __(cmp imm0,#0)
        __(bne 1f)
/* lexpr count was 0; vpop the arg regs that  */
/* were vpushed by the caller  */
        __(vpop_argregs())
        __(ret)

/* vpush args from the lexpr until we have only  */
/* three left, then assign them to arg_x, arg_y,  */
/* and arg_z.  */
8:
        __(cmp imm0,#4<<fixnumshift)
        __(sub imm0,imm0,#fixnumone)
        __(ldr arg_z,[imm1,#-node_size]!)
        __(vpush1(arg_z))
9:
        __(bne 8b)
        __(ldr arg_x,[imm1,#-node_size*1])
        __(ldr arg_y,[imm1,#-node_size*2])
        __(ldr arg_z,[imm1,#-node_size*3])
        __(ret)

/* lexpr count is two: set arg_y, arg_z from the  */
/* lexpr, maybe vpop arg_x  */
2:
        __(cmp nargs,#2*node_size)
        __(ldr arg_y,[imm1,#-node_size*1])
        __(ldr arg_z,[imm1,#-node_size*2])
        __(beq 9f)  /* return if (new) nargs = 2  */
        __(vpop1(arg_x))
9:      __(ret)

/* lexpr count is one: set arg_z from the lexpr,  */
/* maybe vpop arg_y, arg_x  */
1: 
        __(cmp nargs,#2*node_size)
        __(ldr arg_z,[imm1,#-node_size])
        __(blt 9f)  /* return if (new) nargs < 2  */
        __(vpop1(arg_y))
        __(beq 9f)  /* return if (new) nargs = 2  */
        __(vpop1(arg_x))
0:      __(ret)


_spentry(reset)
        __(nop)
        __(ref_nrs_value(temp0,toplcatch))
        __(mov temp1,#XSTKOVER)
        __(vpush1(temp0))
        __(vpush1(temp1))
        __(set_nargs(1))
        __(b _SPthrow)


/* "slide" nargs worth of values up the vstack.  IMM0 contains  */
/* the difference between the current VSP and the target.  */
_spentry(mvslide)
        __(cmp nargs,#0)
        __(mov temp1,nargs)
        __(add imm1,vsp,nargs)
        __(add imm1,imm1,imm0)
        __(add imm0,vsp,nargs)
        __(beq 2f)
1:
        __(subs temp1,temp1,#node_size)
        __(ldr temp0,[imm0,#-node_size]!)
        __(str temp0,[imm1,#-node_size]!)
        __(bne 1b)
2:
        __(mov vsp,imm1)
        __(ret)

                      
_spentry(save_values)
        __(mov temp1,#0)
        __(mov arg_x,sp)
local_label(save_values_to_tsp):
        __(add imm1,nargs,#node_size*2)
        __(dnode_align(imm0,imm1,node_size))
        __(movk imm1,#(subtag_u64_vector << 8),lsl #48)
        __(stack_allocate_zeroed_ivector(imm1,imm0))
        __(cmp temp1,#0)
        __(mov imm1,#subtag_simple_vector)
        __(load_marker(arg_y,tag_stack_alloc))
        __(strb gpr32(imm1),[sp,#7])
        __(mov temp0,sp)
        __(stp arg_y,arg_x,[sp,#-dnode_size]!)
        __(str temp1,[temp0,#mvcall_older_value_set])
        __(cbz temp1,0f)
        __(str temp0,[temp1,#mvcall_younger_value_set])
0:
        __(add temp0,temp0,#node_size+8)
        __(mov imm0,#0)
        __(b 2f)
1:      __(vpop1(temp1))
        __(str temp1,[temp0],#node_size)
        __(add imm0,imm0,#node_size)
2:      __(cmp imm0,nargs)
        __(bne 1b)
        __(ret)
        
_spentry(add_values)
        __(cmp nargs,#0)
        __(ldr arg_x,[sp,#node_size])
        __(beq 9f)
        __(add sp,sp,#dnode_size)
        __(mov temp1,sp)
        __(b local_label(save_values_to_tsp))
9:      __(ret)
        
/* Like misc_alloc (a LOT like it, since it does most of the work), but takes  */
/* an initial-value arg in arg_z, element_count in arg_x, subtag in arg_y.  */
/* Calls out to %init-misc, which does the rest of the work.  */

_spentry(misc_alloc_init)
        /* Bug 135: Save initval to vstack — temp2 (x12) is NOT callee-saved
           on ARM64 and gets clobbered by SPmisc_alloc.
           Must vpush BEFORE build_lisp_frame so that restore_lisp_frame
           preserves the modified vsp. */
        __(vpush1(arg_z))    /* push initval to vstack */
        __(build_lisp_frame())
        __(mov arg_z,arg_y)  /* subtag  */
        __(mov arg_y,arg_x)  /* element-count  */
        __(bl _SPmisc_alloc)
        __(restore_lisp_frame())
        __(vpop1(arg_y))     /* pop initval from vstack */
initialize_vector:              
        __(ref_nrs_symbol(fname,init_misc))
        __(set_nargs(2))
        __(jump_fname())

/* As in stack_misc_alloc above, only with a non-default initial-value.  */
/* Note that this effectively inlines _SPstack_misc_alloc. */                
 
_spentry(stack_misc_alloc_init)
        __(tst arg_x,#unsigned_byte_24_mask)
        __(beq 1f)
        __(uuo_error_reg_not_xtype(arg_x,xtype_unsigned_byte_24))
1:              
        __(unbox_fixnum(imm0,arg_y))
        __(tst imm0,#gvector_tag_mask)
        __(beq stack_misc_alloc_init_ivector)
        /* gvector: byte_count = element_count * node_size (8) */
        __(lsl imm1,arg_x,#3)
        __(dnode_align(imm1,imm1,node_size))
        __(ldr temp1,[rcontext,#tcr.cs_limit])
        __(sub temp0,sp,imm1)
        __(cmp temp0,temp1)
        __(bls stack_misc_alloc_init_no_room)
        __(mov imm0,arg_x)
        __(movk imm0,#(subtag_u32_vector << 8),lsl #48)
        __(load_marker(temp0,tag_stack_alloc))
        __(mov temp1,sp)
        __(stack_allocate_zeroed_ivector(imm0,imm1))
        __(unbox_fixnum(imm0,arg_y))
        __(strb gpr32(imm0),[sp,#7])
        __(mov arg_y,arg_z)
        __(add arg_z,sp,#node_size)
        __(orr arg_z,arg_z,#(fulltag_misc << tag_shift))
        __(stp temp0,temp1,[sp,#-dnode_size]!)
        __(b initialize_vector)

 
_spentry(popj)
        .globl C(popj)
C(popj):
        __(return_lisp_frame())




/* arg_z should be of type (UNSIGNED-BYTE 64);  */
/* return unboxed value in imm0 */


_spentry(getu64)
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(branch_if_negative(arg_z,0f))
        __(unbox_fixnum(imm0,arg_z))
        __(ret)
0:              
        __(uuo_error_reg_not_xtype(arg_z,xtype_u64))
1:
        __(extract_lisptag(imm0,arg_z))
        __(cmp imm0,#tag_misc)
        __(bne 0b)
        __(getvheader(imm0,arg_z))
        __(make_header(imm1,2,bignum_header))
        __(cmp imm0,imm1)
        __(bne 2f)
        __(ldr imm0,[arg_z,#misc_data_offset])
        __(branch_if_negative(imm0,0b))
        __(ret)
2:      __(make_header(imm1,3,bignum_header))
        __(cmp imm0,imm1)
        __(bne 0b)
        __(vref32(imm1,arg_z,2))
        __(ldr imm0,[arg_z,#misc_data_offset])
        __(cbnz imm1,0b)
        __(ret)

         
/* arg_z should be of type (SIGNED-BYTE 64);  */
/*    return unboxed value in imm0  */

/* Bug 161: On ARM64 with fixnumshift=0, unbox_fixnum is identity (mov imm0,arg_z).
   branch_if_fixnum uses its scratch register (imm0) for the fixnum test,
   clobbering the unboxed value to 0.  Fix: test first, then unbox (like getu64). */
_spentry(gets64)
        __(branch_if_not_fixnum(arg_z,1f,imm0))
        __(unbox_fixnum(imm0,arg_z))
        __(ret)
1:
        __(extract_lisptag(imm0,arg_z))
        __(cmp imm0,#tag_misc)
        __(bne 2f)
        __(getvheader(imm0,arg_z))
        __(make_header(imm1,2,bignum_header))
        __(cmp imm0,imm1)
        __(bne 2f)
        __(ldr imm0,[arg_z,#misc_data_offset])
        __(ret)
2:      __(uuo_error_reg_not_xtype(arg_z,xtype_s64))


/* arg_z should be of type (SIGNED-BYTE 32);  */
/*    return unboxed value in imm0.  */
/* On ARM64, every s32 fits in a fixnum; this is a stub like x86-64.  */

_spentry(gets32)
        __(hlt #0)
_endsubp(gets32)

/* arg_z should be of type (UNSIGNED-BYTE 32);  */
/*    return unboxed value in imm0.  */
/* On ARM64, every u32 fits in a fixnum; this is a stub like x86-64.  */

_spentry(getu32)
        __(hlt #0)
_endsubp(getu32)


/* Unsigned 64-bit by 64-bit division.  */
/* On entry: imm0 = 64-bit dividend, imm2 = 64-bit divisor.  */
/* On exit:  imm0 = quotient, imm1 = remainder.  */

_spentry(udiv64by32)
        __(cbz imm2,0f)
        __(mov imm1,imm0)
        __(udiv imm0,imm1,imm2)
        __(msub imm1,imm0,imm2,imm1)
        __(ret)
0:
        __(build_lisp_frame())
        __(bl _SPmakeu64)
        __(mov arg_y,#XDIVZRO)
        __(set_nargs(2))
        __(restore_lisp_frame())
        __(b _SPksignalerr)
_endsubp(udiv64by32)


/* on entry: arg_z = symbol.  On exit, arg_z = value (possibly */
/* unbound_marker), arg_y = symbol, imm1 = symbol.binding-index  */
_spentry(specref)
        __(ldr imm1,[arg_z,#symbol.binding_index])
        /* Bug 124: binding-index is already a byte offset */
        __(ldr imm0,[rcontext,#tcr.tlb_limit])
        __(cmp imm1,imm0)
        __(ldr temp0,[rcontext,#tcr.tlb_pointer])
        __(mov arg_y,arg_z)
        __(csel imm1,xzr,imm1,hs)
        __(ldr arg_z,[temp0,imm1])
        __(cmp_tag_to_marker(arg_z,imm0,tag_no_thread_local_binding))
        __(bne 9f)
        __(ldr arg_z,[arg_y,#symbol.vcell])
9:      __(ret)

_spentry(specrefcheck)
        __(ldr imm1,[arg_z,#symbol.binding_index])
        /* Bug 124: binding-index is already a byte offset */
        __(ldr imm0,[rcontext,#tcr.tlb_limit])
        __(cmp imm1,imm0)
        __(csel imm1,xzr,imm1,hs)
        __(ldr imm0,[rcontext,#tcr.tlb_pointer])
        __(mov arg_y,arg_z)
        __(ldr arg_z,[imm0,imm1])
        __(cmp_tag_to_marker(arg_z,imm0,tag_no_thread_local_binding))
        __(bne 1f)
        __(ldr arg_z,[arg_y,#symbol.vcell])
1:      __(cmp_tag_to_marker(arg_z,imm0,tag_unbound))
        __(bne 9f)
        __(uuo_error_unbound(arg_y))
9:      __(ret)

/* arg_y = special symbol, arg_z = new value.          */
_spentry(specset)
        __(ldr imm1,[arg_y,#symbol.binding_index])
        /* Bug 124: binding-index is already a byte offset */
        __(ldr imm0,[rcontext,#tcr.tlb_limit])
        __(ldr imm2,[rcontext,#tcr.tlb_pointer])
        __(cmp imm1,imm0)
        __(csel imm1,xzr,imm1,hs)
        __(ldr temp1,[imm2,imm1])
        __(cmp_tag_to_marker(temp1,imm0,tag_no_thread_local_binding))
        __(beq 1f)
        __(str arg_z,[imm2,imm1])
        __(b 9f)
1:      __(mov arg_x,arg_y)
        __(mov arg_y,#1)
        __(b _SPgvset)
9:      __(ret)

	


/* */
/* As per mvpass above, but in this case fname is known to be a */
/* symbol. */

_spentry(mvpasssym)
        __(cmp nargs,#node_size*nargregs)
        __(mov imm1,vsp)
        __(ble 0f)
        __(sub imm1,imm1,#node_size*nargregs)
        __(add imm1,imm1,nargs)
0:
	__(build_lisp_frame(imm1))
        __(ref_global(lr,ret1val_addr,imm0))
        __(jump_fname())

_spentry(unbind)
        __(ldr imm1,[rcontext,#tcr.db_link])
        __(ldr temp0,[rcontext,#tcr.tlb_pointer])   
        __(ldr imm0,[imm1,#binding.sym])
        __(ldr temp1,[imm1,#binding.val])
        __(ldr imm1,[imm1,#binding.link])
        __(str temp1,[temp0,imm0])
        __(str imm1,[rcontext,#tcr.db_link])
        __(ret)

/* Clobbers imm1,temp0,arg_x, arg_y */        
_spentry(unbind_n)
        __(ldr imm1,[rcontext,#tcr.db_link])
        __(ldr arg_x,[rcontext,#tcr.tlb_pointer])
1:      __(ldr temp0,[imm1,#binding.sym])
        __(ldr arg_y,[imm1,#binding.val])
        __(ldr imm1,[imm1,#binding.link])
        __(subs imm0,imm0,#1)
        __(str arg_y,[arg_x,temp0])
        __(bne 1b)
        __(str imm1,[rcontext,#tcr.db_link])
        __(ret)

/* */
/* Clobbers imm1,temp0,arg_x, arg_y */

_spentry(unbind_to)
        do_unbind_to(imm1,temp1,arg_x,arg_y)
        __(ret)
 

 
/* */
/* Restore the special bindings from the top of the tstack,  */
/* leaving the tstack frame allocated.  */
/* Note that there might be 0 saved bindings, in which case  */
/* do nothing.  */
/* Note also that this is -only- called from an unwind-protect  */
/* cleanup form, and that .SPnthrowXXX is keeping one or more  */
/* values in a frame on top of the tstack.  */
/*  */
                         
_spentry(progvrestore)
        __(skip_stack_vector(imm0,imm1,sp,imm2,imm3))
        __(ldr imm0,[imm0,#lisp_frame.size+(9*8)+node_size]) /* 7*8 = size of saved FPR vector, with header */
        __(cmp imm0,#0)
        __(unbox_fixnum(imm0,imm0))
        __(bne _SPunbind_n)
        __(ret)

/* Bind CCL::*INTERRUPT-LEVEL* to 0.  If its value had been negative, check  */
/* for pending interrupts after doing so.  */
_spentry(bind_interrupt_level_0)
        __(ldr temp1,[rcontext,#tcr.tlb_pointer])
        __(ldr temp0,[temp1,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(cmp temp0,#0)
        __(mov imm1,#INTERRUPT_LEVEL_BINDING_INDEX)
        __(vpush1(temp0))
        __(vpush1(imm1))
        __(vpush1(imm0))
        __(mov imm0,#0)
        __(str imm0,[temp1,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(str vsp,[rcontext,#tcr.db_link])
        __(bge 9f)
        __(ldr temp0,[rcontext,#tcr.interrupt_pending])
        __(cmp temp0,#0)
        __(ble 9f)
        __(uuo_interrupt_now(al))
9:      __(ret)
	
/* Bind CCL::*INTERRUPT-LEVEL* to the fixnum -1.  (This has the effect */
/* of disabling interrupts.)  */
_spentry(bind_interrupt_level_m1)
        __(mov imm2,#-fixnumone)
        __(mov imm1,#INTERRUPT_LEVEL_BINDING_INDEX)
        __(ldr temp1,[rcontext,#tcr.tlb_pointer])
        __(ldr temp0,[temp1,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(vpush1(temp0))
        __(vpush1(imm1))
        __(vpush1(imm0))
        __(str imm2,[temp1,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(str vsp,[rcontext,tcr.db_link])
        __(ret)
	

/* Bind CCL::*INTERRUPT-LEVEL* to the value in arg_z.  If that value's 0, */
/* do what _SPbind_interrupt_level_0 does  */
_spentry(bind_interrupt_level)
        __(cmp arg_z,#0)
        __(mov imm1,#INTERRUPT_LEVEL_BINDING_INDEX)
        __(ldr temp1,[rcontext,#tcr.tlb_pointer])
        __(ldr temp0,[temp1,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(beq _SPbind_interrupt_level_0)
        __(vpush1(temp0))
        __(vpush1(imm1))
        __(vpush1(imm0))
        __(str arg_z,[temp1,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(str vsp,[rcontext,#tcr.db_link])
        __(ret)

/* Unbind CCL::*INTERRUPT-LEVEL*.  If the value changes from negative to */
/* non-negative, check for pending interrupts.  This is often called in */
/* a context where nargs is significant, so save and restore nargs around */
/* any interrupt polling  */
         
_spentry(unbind_interrupt_level)
        __(ldr gpr32(imm0),[rcontext,#tcr.flags])
        __(ldr temp2,[rcontext,#tcr.tlb_pointer])
        __(tst imm0,#1<<TCR_FLAG_BIT_PENDING_SUSPEND)
        __(ldr imm0,[rcontext,#tcr.db_link])
        __(ldr temp0,[temp2,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(bne 5f)
0:      
        __(ldr temp1,[imm0,#binding.val])
        __(ldr imm0,[imm0,#binding.link])
        __(str temp1,[temp2,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(str imm0,[rcontext,#tcr.db_link])
        __(cmp temp0,#0)
        __(bge 9f)
        __(cmp temp1,#0)
        __(blt 9f)
        __(check_enabled_pending_interrupt(imm0,1f))
1:              
9:      __(ret)
5:       /* Missed a suspend request; force suspend now if we're restoring
          interrupt level to -1 or greater */
        __(cmp temp0,#-2<<fixnumshift)
        __(bne 0b)
        __(ldr imm0,[imm1,#binding.val])
        __(cmp imm0,temp0)
        __(beq 0b)
        __(mov imm0,#1<<fixnumshift)
        __(str imm0,[temp2,#INTERRUPT_LEVEL_BINDING_INDEX])
        __(suspend_now())
        __(b 0b)
 
 
/* arg_x = array, arg_y = i, arg_z = j. Typecheck everything.
    We don't know whether the array is alleged to be simple or
   not, and don't know anythng about the element type.  */
_spentry(aref2)
        __(trap_unless_fixnum(arg_y))
        __(trap_unless_fixnum(arg_z))
        __(extract_typecode(imm2,arg_x))
        __(cmp imm2,#subtag_arrayH)
        __(bne 0f)
        __(ldr imm1,[arg_x,#arrayH.rank])
        __(cmp imm1,#2<<fixnumshift)
        __(beq 1f)
0:
        __(uuo_error_reg_not_xtype(arg_x,xtype_array2d))
1:
        /* It's a 2-dimensional array.  Check bounds */
        __(ldr imm0,[arg_x,#arrayH.dim0])
        __(cmp arg_y,imm0)
        __(blo 2f)
        __(uuo_error_array_axis_bounds(arg_y,imm0,0))
2:
        __(ldr imm0,[arg_x,#arrayH.dim0+node_size])
        __(cmp arg_z,imm0)
        __(blo 3f)
        __(uuo_error_array_axis_bounds(arg_z,imm0,1))
3:
        __(unbox_fixnum(imm0,imm0))
	__(madd arg_z,arg_y,imm0,arg_z)
        /* arg_z is now row-major-index; get data vector and
           add in possible offset */
        __(mov arg_y,arg_x)
0:      __(ldr imm0,[arg_y,#arrayH.displacement])
        __(ldr arg_y,[arg_y,#arrayH.data_vector])
        __(extract_subtag(imm1,arg_y))
        __(cmp imm1,#subtag_vectorH)
        __(add arg_z,arg_z,imm0)
        __(bgt C(misc_ref_common))
        __(b 0b)
 
/* temp0 = array, arg_x = i, arg_y = j, arg_z = k */
_spentry(aref3)
        __(trap_unless_fixnum(arg_x))
        __(trap_unless_fixnum(arg_y))
        __(trap_unless_fixnum(arg_z))
        __(extract_typecode(imm2,temp0))
        __(cmp imm2,#subtag_arrayH)
        __(bne 0f)
        __(ldr imm1,[temp0,#arrayH.rank])
        __(cmp imm1,#3<<fixnumshift)
        __(beq 1f)
0:
        __(uuo_error_reg_not_xtype(temp0,xtype_array3d))
1:
        /* It's a 3-dimensional array.  Check bounds */
        __(ldr imm2,[temp0,#arrayH.dim0+(node_size*2)])
        __(ldr imm1,[temp0,#arrayH.dim0+node_size])
        __(ldr imm0,[temp0,#arrayH.dim0])
        __(cmp arg_z,imm2)
        __(blo 2f)
        __(uuo_error_array_axis_bounds(arg_z,imm2,2))
2:
        __(cmp arg_y,imm1)
        __(blo 3f)
        __(uuo_error_array_axis_bounds(arg_y,imm1,1))
3:
        __(cmp arg_x,imm0)
        __(blo 4f)
        __(uuo_error_array_axis_bounds(arg_x,imm0,0))
4:
        __(unbox_fixnum(imm2,imm2))
        __(unbox_fixnum(imm1,imm1))
	/* (+ (* i dim1 dim2) (* j dim2) k) */
	__(mul imm1,imm2,imm1)
	__(madd imm2,arg_y,imm2,arg_z)	/* imm2 now a fixnum */
	__(madd arg_z,arg_x,imm1,imm2)
        __(mov arg_y,temp0)
0:      __(ldr arg_x,[arg_y,#arrayH.displacement])
        __(ldr arg_y,[arg_y,#arrayH.data_vector])
        __(extract_subtag(imm1,arg_y))
        __(cmp imm1,#subtag_vectorH)
        __(add arg_z,arg_x,arg_z)
        __(bgt C(misc_ref_common))
        __(b 0b)




/* As for aref2 above, but temp0 = array, arg_x = i, arg_y = j, arg_z = newval */
_spentry(aset2)
        __(extract_typecode(imm0,temp0))
        __(cmp imm0,#subtag_arrayH)
        __(bne 0f)
        __(ldr imm0,[temp0,#arrayH.rank])
        __(cmp imm0,#2<<fixnumshift)
        __(beq 1f)
0:
        __(uuo_error_reg_not_xtype(temp0,xtype_array2d))
1:              
        __(trap_unless_fixnum(arg_x))
        __(trap_unless_fixnum(arg_y))
        /* It's a 2-dimensional array.  Check bounds */
        __(ldr imm0,[temp0,#arrayH.dim0])
        __(cmp arg_x,imm0)
        __(blo 2f)
        __(uuo_error_array_axis_bounds(arg_x,imm0,0))
2:
        __(ldr imm0,[temp0,#arrayH.dim0+node_size])
        __(cmp arg_y,imm0)
        __(blo 3f)
        __(uuo_error_array_axis_bounds(arg_y,imm0,1))
3:
        __(unbox_fixnum(imm0,imm0))
	__(madd arg_y,arg_x,imm0,arg_y)
        /* arg_y is now row-major-index; get data vector and
           add in possible offset */
        __(mov arg_x,temp0)
0:      __(ldr imm0,[arg_x,#arrayH.displacement])
        __(ldr arg_x,[arg_x,#arrayH.data_vector])
        __(extract_subtag(imm1,arg_x))
        __(cmp imm1,#subtag_vectorH)
        __(add arg_y,arg_y,imm0)
        __(bgt C(misc_set_common))
        __(b 0b)

                 
/* temp1 = array, temp0 = i, arg_x = j, arg_y = k, arg_z = new */        
_spentry(aset3)
        __(extract_typecode(imm0,temp1))
        __(cmp imm0,#subtag_arrayH)
        __(bne 0f)
        __(ldr imm0,[temp1,#arrayH.rank])
        __(cmp imm0,#3<<fixnumshift)
        __(beq 1f)
0:
        __(uuo_error_reg_not_xtype(temp1,xtype_array3d))
1:              
        __(trap_unless_fixnum(temp0))
        __(trap_unless_fixnum(arg_x))
        __(trap_unless_fixnum(arg_y))
        /* It's a 3-dimensional array.  Check bounds */
        __(ldr imm2,[temp1,#arrayH.dim0+(node_size*2)])
        __(ldr imm1,[temp1,#arrayH.dim0+node_size])
        __(ldr imm0,[temp1,#arrayH.dim0])
        __(cmp arg_y,imm2)
        __(blo 2f)
        __(uuo_error_array_axis_bounds(arg_y,imm2,2))
2:
        __(cmp arg_x,imm1)
        __(blo 3f)
        __(uuo_error_array_axis_bounds(arg_x,imm1,1))
3:
        __(cmp temp0,imm0)
        __(blo 4f)
        __(uuo_error_array_axis_bounds(temp0,imm0,0))
4:              
	__(unbox_fixnum(imm1,imm1))
	__(unbox_fixnum(imm2,imm2))
	/* (+ (* i dim1 dim2) (* j dim2) k) */
	__(mul imm1,imm2,imm1)
	__(madd imm2,arg_x,imm2,arg_y)	/* imm2 now a fixnum */
	__(madd arg_y,temp0,imm1,imm2)
        __(mov arg_x,temp1)
0:      __(ldr temp0,[arg_x,#arrayH.displacement])
        __(ldr arg_x,[arg_x,#arrayH.data_vector])
        __(extract_subtag(imm1,arg_x))
        __(cmp imm1,#subtag_vectorH)
        __(add arg_y,arg_y,temp0)
        __(bgt C(misc_set_common))
        __(b 0b)


/* Treat the last (- nargs imm0) values on the vstack as keyword/value  */
/* pairs.  There'll be arg_z keyword arguments.  arg_y contains flags  */
/* that indicate whether &allow-other-keys was specified and whether  */
/* or not to leave the keyword/value pairs on the vstack for an &rest  */
/* argument.  Element 2 of the function in fn contains a vector of keyword.  */
/* If the number of arguments is greater than imm0, the difference must  */
/* be even.  */
/* All arg regs have been vpushed and the calling function has built a */
/* stack frame.  next_method_context must be preserved, as must the incoming */
/* key/value pairs and their number if we're going to make an &rest arg. */
           

define(`keyword_flags',`arg_y')
define(`key_value_count',`arg_z')

define(`keyword_flag_allow_other_keys',`(fixnumone<<0)')
define(`keyword_flag_seen_allow_other_keys',`(fixnumone<<1)')
define(`keyword_flag_rest',`(fixnumone<<2)')
define(`keyword_flag_unknown_keyword_seen',`(fixnumone<<3)')
define(`keyword_flag_current_aok',`(fixnumone<<4)')

_spentry(keyword_bind)
        new_local_labels()        
        __(subs key_value_count,nargs,imm0)
        __(bpl 0f)
        __(mov key_value_count,#0)
0:
        __(tst key_value_count,#node_size)
        __(bne local_label(odd_keywords))
        __(lsr imm1,key_value_count,#node_shift)
        __(movk imm1,#(subtag_u64_vector << 8),lsl #48)
        __(mov imm0,key_value_count)
        __(add imm0,imm0,#dnode_size) /* we know count is even */
        __(stack_allocate_zeroed_ivector(imm1,imm0))
        __(mov imm0,#subtag_simple_vector)
        __(strb gpr32(imm0),[sp,#7])
        /* Copy key/value pairs in reverse order from the vstack to
           the gvector we just created on the cstack. */
        __(add imm0,vsp,key_value_count) /* src, predecrement */
        __(add imm1,sp,#node_size)       /* dest, postincrement */
        __(mov temp3,key_value_count)
        __(b 1f)
0:      __(ldr arg_x,[imm0,#-node_size]!)
        __(str arg_x,[imm1],#node_size)
1:      __(subs temp3,temp3,#node_size)
        __(bge 0b)
        /* Discard the key/value pairs from the vstack. */
        __(add vsp,vsp,key_value_count)
        __(ldr temp2,[fn,#misc_data_offset+(2*node_size)])
        __(getvheader(imm0,temp2))
        __(header_length(imm0,imm0))
        __(mov temp0,vsp)
        __(mov imm1,rnil)
        /* Push a pair of NILs (value, supplied-p) for each defined keyword */
        __(b 3f)
2:      __(vpush1(imm1))
        __(vpush1(imm1))
3:      __(subs imm0,imm0,#1)
        __(bge 2b)
        /* Save nargs and temp1 so that we can use them in the loop(s) */
        __(stp imm2,temp1,[vsp,#-dnode_size]!)
        /* For each provided key/value pair: if the key is :allow-other-keys
           and that hasn't been seen before, note that it's been seen and
           if the value is non-nil set the allow-other-keys bit in flags.
           Then search for the key in the defined keys vector.  If it's
           not found, note that an undefined keyword was seen by setting
           a bit in keyword_flags ; if it is found, use its position to
           index the table of value/supplied-p pairs that we pushed above.
           If the supplied-p var is already set, do nothing; otherwise,
           set the supplied-p var and value.
           When done, signal an error if we got an unknown keyword, or
           either copy the supplied key/value pairs back to the vstack
           if we're going to cons an &rest arg or discard them if we aren't.
        */
        __(mov imm2,#0)
        __(b local_label(nextvalpairtest))
local_label(nextvalpairloop):
        __(add temp1,sp,#node_size)
        __(ldr temp1,[temp1,imm2])
        __(ref_nrs_symbol(imm1,kallowotherkeys))
        __(cmp temp1,imm1)
        __(bne local_label(current_key_allow_other_keys_handled))
        __(orr keyword_flags,keyword_flags,#keyword_flag_current_aok)
        __(tst keyword_flags,#keyword_flag_seen_allow_other_keys)
        __(bne local_label(current_key_allow_other_keys_handled))
        __(orr keyword_flags,keyword_flags,#keyword_flag_seen_allow_other_keys)
        /* Fortunately, we know what the keyword is.  Need to check the
           value here, and don't have a lot of free registers ... */
        __(add temp1,sp,#2*node_size)
        __(ldr temp1,[temp1,imm2])
        __(cmp temp1,rnil)
        __(beq 0f)
        __(orr keyword_flags,keyword_flags,#keyword_flag_allow_other_keys)
0:
        __(mov temp1,imm1)      /* from comparison above */
local_label(current_key_allow_other_keys_handled):
        __(getvheader(imm0,temp2))
        __(header_length(arg_x,imm0))
        __(lsl arg_x,arg_x,#node_shift)   /* count → byte offset (fixnumshift=0) */
        __(add imm0,arg_x,#misc_data_offset)
        __(b local_label(defined_keyword_compare_test))
local_label(defined_keyword_compare_loop):
        __(ldr arg_x,[temp2,imm0])
        __(cmp arg_x,temp1)
        __(bne local_label(defined_keyword_compare_test))
        __(sub imm0,imm0,#misc_data_offset)
        __(b local_label(defined_keyword_found))
local_label(defined_keyword_compare_test):
        __(sub imm0,imm0,#node_size)
        __(cmp imm0,#misc_data_offset)
        __(bge local_label(defined_keyword_compare_loop))
        /* keyword wasn't defined.  Note that ... */
        __(tst keyword_flags,#keyword_flag_current_aok)
        __(beq 0f)
        __(bic keyword_flags,keyword_flags,#keyword_flag_current_aok)
        __(b local_label(nextkeyvalpairnext))
0:
        __(orr keyword_flags,keyword_flags,#keyword_flag_unknown_keyword_seen)
        __(b local_label(nextkeyvalpairnext))
local_label(defined_keyword_found):
        /* imm0 = byte position of keyword in vector (after subtracting misc_data_offset).
           Each keyword maps to 2 slots in value table (value + supplied-p).
           On ARM64: each slot is node_size bytes, so multiply by 2 for pair stride. */
        __(sub imm0,temp0,imm0,lsl #1)
        __(ldr arg_x,[imm0,#-(2*node_size)])
        __(cmp arg_x,rnil) /* seen this keyword yet ? */
        __(bne local_label(nextkeyvalpairnext))
        __(add arg_x,arg_x,#t_offset)
        __(str arg_x,[imm0,#-(2*node_size)])
        __(add temp1,sp,#(2*node_size))
        __(ldr temp1,[temp1,imm2])
        __(str temp1,[imm0,#-node_size])
local_label(nextkeyvalpairnext):
        __(add imm2,imm2,#(2*node_size))
local_label(nextvalpairtest):
        __(cmp imm2,key_value_count)
        __(bne local_label(nextvalpairloop))
        __(ldp imm2,temp1,[vsp],#dnode_size)
        /* If unknown keywords and that's not allowed, signal error.
           Otherwise, discard the stack-consed vector and return,
           possibly after having copied the vector's contents back
           to the vstack so that an &rest arg can be constructed.
        */
        __(tst keyword_flags,#keyword_flag_unknown_keyword_seen)
        __(beq 0f)
        __(tst keyword_flags,#keyword_flag_allow_other_keys)
        __(beq local_label(badkeys))
0:      __(tst keyword_flags,#keyword_flag_rest)
        __(beq local_label(discard_stack_vector))
        __(mov imm0,#0)
        __(add temp2,sp,#node_size)
        __(b 2f)
1:      __(ldr arg_x,[temp2],#node_size)
        __(vpush1(arg_x))
        __(add imm0,imm0,#node_size)
2:      __(cmp imm0,key_value_count)
        __(bne 1b)
local_label(discard_stack_vector):
        __(add key_value_count,key_value_count,#dnode_size)
        __(add sp,sp,key_value_count)
        __(ret)               /* it's finally over ! */

local_label(badkeys):   /* Disturbingly similar to the &rest case */
        __(mov nargs,#0)
        __(add temp2,sp,#node_size)
        __(mov vsp,temp0)
        __(b 1f)
0:      __(ldr arg_x,[temp2],#node_size)
        __(vpush1(arg_x))
        __(add nargs,nargs,#node_size)
1:      __(cmp nargs,key_value_count)
        __(bne 0b)
        /* Lose the stack vector */
        __(add key_value_count,key_value_count,#dnode_size)
        __(add sp,sp,key_value_count)
local_label(error_exit):                
        __(bl _SPconslist)
        __(mov arg_y,#XBADKEYS)
        __(set_nargs(2))
        __(b _SPksignalerr)
local_label(odd_keywords):       
        __(mov nargs,key_value_count)
        __(b local_label(error_exit))


/* Unsigned 32-bit division.  */
/* On entry: imm0 = unsigned 32-bit dividend, imm1 = unsigned 32-bit divisor.  */
/* On exit:  imm0 = quotient, imm1 = remainder.  */

_spentry(udiv32)
        __(cbz gpr32(imm1),0f)
        __(mov imm2,imm0)
        __(udiv gpr32(imm0),gpr32(imm2),gpr32(imm1))
        __(msub gpr32(imm1),gpr32(imm0),gpr32(imm1),gpr32(imm2))
        __(ret)
0:
        __(mov arg_z,imm0)
        __(mov arg_y,#XDIVZRO)
        __(set_nargs(2))
        __(b _SPksignalerr)
_endsubp(udiv32)

/* Signed 32-bit division.  */
/* On entry: imm0 = signed 32-bit dividend, imm1 = signed 32-bit divisor.  */
/* On exit:  imm0 = quotient, imm1 = remainder.  */

_spentry(sdiv32)
        __(cbz gpr32(imm1),0f)
        __(mov imm2,imm0)
        __(sdiv gpr32(imm0),gpr32(imm2),gpr32(imm1))
        __(msub gpr32(imm1),gpr32(imm0),gpr32(imm1),gpr32(imm2))
        __(ret)
0:
        __(sxtw arg_z,gpr32(imm0))
        __(mov arg_y,#XDIVZRO)
        __(set_nargs(2))
        __(b _SPksignalerr)
_endsubp(sdiv32)

_spentry(eabi_ff_callhf)
        /* Load d0-d7 from the c-frame float area (elements 0-7).
           Data starts at sp + dnode_size (past header + prevsp). */
        __(add imm0,sp,#dnode_size)
        __(ldp d0,d1,[imm0])
        __(ldp d2,d3,[imm0,#16])
        __(ldp d4,d5,[imm0,#32])
        __(ldp d6,d7,[imm0,#48])
        /* Strip 8 float slots (64 bytes) from the c-frame.
           Create new header+prevsp at sp+64, then set SP there. */
        __(ldp imm0,imm1,[sp])
        __(sub imm0,imm0,#8)
        __(add imm2,sp,#8<<3)
        __(stp imm0,imm1,[imm2])
        __(mov sp,imm2)
/* ARM64 ff-call: Save Lisp state on the value stack (not a C-stack lisp
   frame), load C args from the c-frame without advancing sp, set sp to
   prevsp (clean stack), then call C.  This avoids the lisp-frame-inside-
   c-frame overlap that corrupted savelr when the c-frame was small.  */
_spentry(eabi_ff_call)
        /* Save Lisp state on vsp: last_lisp_frame, arg_x, temp0, temp1,
           temp2(=nfn), lr — 6 values. */
        __(ldr arg_y,[rcontext,#tcr.last_lisp_frame])
        __(sub vsp,vsp,#6*node_size)
        __(stp arg_y,arg_x,[vsp])
        __(stp temp0,temp1,[vsp,#2*node_size])
        __(stp temp2,lr,[vsp,#4*node_size])
        __(str vsp,[rcontext,#tcr.save_vsp])
        __(str allocptr,[rcontext,#tcr.save_allocptr])
        __(mov temp0,sp)
        __(str temp0,[rcontext,#tcr.last_lisp_frame])
        /* x28 (rcontext) and x29 (fp) are callee-saved in AAPCS64,
           so they are preserved across the C call automatically. */
        /* Unbox the function pointer from arg_z */
        __(test_fixnum(imm2,arg_z))
        __(cbnz imm2,0f)
        __(asr imm1,arg_z,#fixnumshift)
        __(b 1f)
0:      __(ldr imm1,[arg_z,#misc_data_offset])
1:
        __(mov imm0,#TCR_STATE_FOREIGN)
        __(str imm0,[rcontext,#tcr.valence])
        __(mov x16,imm1)
        /* Load integer args from c-frame data area using temp3 as pointer.
           Don't advance sp — we'll set it to prevsp for a clean C stack. */
        __(add temp3,sp,#dnode_size)
        __(ldp imm0,imm1,[temp3])
        __(ldp imm2,imm3,[temp3,#2*node_size])
        __(ldp imm4,imm5,[temp3,#4*node_size])
        __(ldp rnil,rt,[temp3,#6*node_size])
        /* Set sp to prevsp (original sp before c-frame allocation).
           The C function gets a clean, properly-aligned stack. */
        __(ldr temp3,[sp,#node_size])
        __(mov sp,temp3)
        __(blr x16)
        /* Back from foreign call.  x0 holds the C return value.
           Restore lisp state from vsp (not from C stack). */
        __(fmov d31,xzr)
        __(mov temp1,#0)
        __(mov temp2,#0)
        __(mov arg_z,#0)
        __(mov arg_y,#0)
        __(mov arg_x,#0)
        __(load_nil(rnil))
        __(load_t(rt,rnil))
        __(load_voidptr(allocptr))
        /* rcontext (x28) preserved by callee-saved convention */
        __(mov imm2,#0)
        __(str imm2,[rcontext,#tcr.valence])
        __(ldr allocptr,[rcontext,#tcr.save_allocptr])
        __(ldr vsp,[rcontext,#tcr.save_vsp])
        /* Restore saved values from vsp */
        __(ldp arg_y,arg_x,[vsp])
        __(ldp temp0,temp1,[vsp,#2*node_size])
        __(ldp temp2,lr,[vsp,#4*node_size])
        __(add vsp,vsp,#6*node_size)
        __(str arg_y,[rcontext,#tcr.last_lisp_frame])
        __(check_pending_interrupt(imm2))
        __(ret)

/* Stub: makes32 — box a signed 32-bit value.
   On ARM64 with fixnumshift=0, 32-bit values are fixnums.
   imm0 = unboxed s32 → arg_z = fixnum (identity on ARM64). */
_spentry(makes32)
        __(sxtw arg_z,imm0)
        __(ret)

/* Stub: makeu32 — box an unsigned 32-bit value.
   On ARM64 with fixnumshift=0, 32-bit values are fixnums. */
_spentry(makeu32)
        __(uxtw arg_z,imm0)
        __(ret)

/* Stub: debind — destructuring-bind.
   TODO: full implementation needed for destructuring-bind. */
_spentry(debind)
        __(hlt #0xDBDB)


_spentry(eabi_callback)
        /* Save integer arg regs (AAPCS64: x0-x7) */
        __(stp imm0,imm1,[sp,#-8*node_size]!)
        __(stp imm2,imm3,[sp,#2*node_size])
        __(stp imm4,nargs,[sp,#4*node_size])
        __(stp rnil,rt,[sp,#6*node_size])
        __(mov imm4,sp)    /* save args pointer */
        __(sub sp,sp,#2*node_size)   /* room for result */
        /* Save float arg regs d0-d7 */
        __(stp d0,d1,[sp,#-64]!)
        __(stp d2,d3,[sp,#16])
        __(stp d4,d5,[sp,#32])
        __(stp d6,d7,[sp,#48])
        /* Save callee-saved regs and lr */
        __(stp imm4,nargs,[sp,#-80]!)
        __(stp rnil,rt,[sp,#16])
        __(stp rclosure_call,fname,[sp,#32])
        __(stp nfn,temp1,[sp,#48])
        __(stp temp0,lr,[sp,#64])
        __(mov imm4,imm0)  /* save original x0 */
        __(box_fixnum(nargs,temp0))
        __(ref_global(temp0,get_tcr))
        __(mov imm0,#1)
        __(blr temp0)
        __(mov rcontext,imm0)
        /* SP is already 16-byte aligned on ARM64 */
        __(mov imm2,sp)
        __(str imm2,[sp,#-dnode_size]!)
        __(ldr imm2,[rcontext,#tcr.last_lisp_frame])
        __(mov imm0,sp)
        __(sub imm0,imm2,imm0)
        __(add imm0,imm0,#node_size)
        __(lsr imm0,imm0,#word_shift)
        __(movk imm0,#(subtag_u64_vector << 8),lsl #48)
        __(stp imm0,imm2,[sp,#-dnode_size]!)
        __(push_foreign_fprs())
        /* Clear FP state */
        __(fmov d31,xzr)
        __(mov arg_x,#0)
        __(mov temp0,#0)
        __(mov temp1,#0)
        __(mov temp2,#0)
        __(load_nil(rnil))
        __(load_t(rt,rnil))
        __(load_voidptr(allocptr))
        __(ldr vsp,[rcontext,#tcr.save_vsp])
        __(mov imm0,#TCR_STATE_LISP)
        __(str imm0,[rcontext,#tcr.valence])
        __(ldr allocptr,[rcontext,#tcr.save_allocptr])
        __(set_nargs(2))
        __(ref_nrs_symbol(fname,callbacks))
        __(ldr nfn,[fname,#symbol.fcell])
        __(ldr lr,[nfn,#_function.entrypoint])
        __(blr lr)
        __(str vsp,[rcontext,#tcr.save_vsp])
        __(ldr imm1,[sp,#(10*8)+node_size])
        __(str imm1,[rcontext,#tcr.last_lisp_frame])
        __(str allocptr,[rcontext,#tcr.save_allocptr])
        __(mov imm0,#TCR_STATE_FOREIGN)
        __(str imm0,[rcontext,#tcr.valence])
        __(pop_foreign_fprs())
        /* Restore sp from saved value */
        __(ldr imm0,[sp,#node_size*2])
        __(mov sp,imm0)
        /* Restore callee-saved regs and lr */
        __(ldp imm4,nargs,[sp])
        __(ldp rnil,rt,[sp,#16])
        __(ldp rclosure_call,fname,[sp,#32])
        __(ldp nfn,temp1,[sp,#48])
        __(ldp temp0,lr,[sp,#64])
        __(add sp,sp,#80)
        /* Skip float save area */
        __(add sp,sp,#64)
        /* Load result double from result area */
        __(ldr d0,[sp])
        /* Restore integer return values */
        __(ldp imm0,imm1,[sp,#2*node_size])
        __(add sp,sp,#10*node_size)
        __(ret)        
                       
/*  EOF, basically  */
	
_startfn(C(misc_ref_common))
        /* imm1 = header subtag (high byte of header word, uvector_header-based) */
        __(and imm0,imm1,#uvector_mask)
        __(cmp imm0,#uvector_header)
        __(bne local_label(misc_ref_invalid))
        __(tst imm1,#gvector_tag_mask)
        __(beq 0f)
        __(cmp imm1,#subtag_function)
        __(bne local_label(misc_ref_node))
        __(getvheader(imm0,arg_y,imm0))
        __(sub imm0,imm0,#1)
        __(ldr imm0,[arg_y,imm0,lsl #3])
        __(cmp arg_z,imm0)
        __(blo local_label(misc_ref_u64))
        __(b local_label(misc_ref_node))
0:      __(and imm1,imm1,#31)
        __(adr imm0,local_label(misc_ref_jmp))
        __(add imm0,imm0,imm1,lsl #2)
        __(br imm0)        

/* Jump table indexed by type_bits & 0x1F (lower 5 bits of header subtag).
   ARM64 TBI ivector type_bits layout:
     define_ivector(name, n) -> type_bits = n*2 (even)
     define_cl_ivector(name, n) -> type_bits = n*2|1 (odd)  */
local_label(misc_ref_jmp):
        __(b local_label(misc_ref_u32))                 /* 0: bignum */
        __(b local_label(misc_ref_s32))                 /* 1: s32_vector */
        __(b local_label(misc_ref_u32))                 /* 2: double_float */
        __(b local_label(misc_ref_u32))                 /* 3: u32_vector */
        __(b local_label(misc_ref_u32))                 /* 4: complex_single_float */
        __(b local_label(misc_ref_single_float_vector)) /* 5: single_float_vector */
        __(b local_label(misc_ref_u32))                 /* 6: complex_double_float */
        __(b local_label(misc_ref_simple_string))       /* 7: simple_string */
        __(b local_label(misc_ref_u32))                 /* 8: xcode_vector */
        __(b local_label(misc_ref_invalid))             /* 9: (unused) */
        __(b local_label(misc_ref_u64))                 /* 10: macptr */
        __(b local_label(misc_ref_s64))                 /* 11: s64_vector */
        __(b local_label(misc_ref_u64))                 /* 12: dead_macptr */
        __(b local_label(misc_ref_u64))                 /* 13: u64_vector */
        __(b local_label(misc_ref_invalid))             /* 14: (unused) */
        __(b local_label(misc_ref_node))                /* 15: fixnum_vector */
        __(b local_label(misc_ref_invalid))             /* 16: (unused) */
        __(b local_label(misc_ref_double_float_vector)) /* 17: double_float_vector */
        __(b local_label(misc_ref_invalid))             /* 18: (unused) */
        __(b local_label(misc_ref_u64))                 /* 19: complex_sf_vector */
        __(b local_label(misc_ref_invalid))             /* 20: (unused) */
        __(b local_label(misc_ref_s8))                  /* 21: s8_vector */
        __(b local_label(misc_ref_invalid))             /* 22: (unused) */
        __(b local_label(misc_ref_u8))                  /* 23: u8_vector */
        __(b local_label(misc_ref_invalid))             /* 24: (unused) */
        __(b local_label(misc_ref_s16))                 /* 25: s16_vector */
        __(b local_label(misc_ref_invalid))             /* 26: (unused) */
        __(b local_label(misc_ref_u16))                 /* 27: u16_vector */
        __(b local_label(misc_ref_invalid))             /* 28: (unused) */
        __(b local_label(misc_ref_u64))                 /* 29: complex_df_vector */
        __(b local_label(misc_ref_invalid))             /* 30: (unused) */
        __(b local_label(misc_ref_bit))                 /* 31: bit_vector */
              
                

local_label(misc_ref_node):        
	/* A node vector.  */
	__(ldr  arg_z,[arg_y,arg_z,lsl #node_shift])
	__(ret)
local_label(misc_ref_single_float_vector):
        __(mov imm1,#tag_single_float<<tag_shift)        
	__(ldr gpr32(imm0),[arg_y,arg_z,lsl #2])
        __(orr arg_z,imm1,imm0)
	__(ret)
local_label(misc_ref_simple_string):
        __(mov imm1,#tag_character<<tag_shift)
	__(ldr gpr32(imm0),[arg_y,arg_z,lsl #2])
	__(orr arg_z,imm1,imm0,lsl #charcode_shift)
	__(ret)
local_label(misc_ref_s32):        
	__(ldrsw arg_z,[arg_y,arg_z,lsl #2])
        __(ret)
local_label(misc_ref_u32):        
	__(ldr gpr32(arg_z),[arg_y,arg_z,lsl #2])
        __(ret)
local_label(misc_ref_u64):      
        __(ldr imm0,[arg_y,arg_z,lsl #3])
        __(b _SPmakeu64)
local_label(misc_ref_s64):      
        __(ldr imm0,[arg_y,arg_z,lsl #3])
        __(b _SPmakes64)
                
local_label(misc_ref_double_float_vector):
        __(ldr d0,[arg_y,arg_z,lsl #3])
	__(mov imm2,#double_float_header<<tag_shift)
        __(add imm2,imm2,#double_float.element_count)
        __(mov imm1,#tag_double_float)
	__(Misc_Alloc_Fixed(arg_z,imm2,double_float.size,imm2))
        __(str d0,[arg_z,#double_float.value])
	__(ret)
local_label(misc_ref_bit):
        __(and imm1,arg_z,#63)
        __(eor imm1,imm1,#63)
        __(lsr imm0,arg_z,#6)
        __(ldr imm2,[arg_y,imm0,lsl #word_shift])
        __(lsr imm2,imm2,imm1)
        __(and arg_z,imm2,#1)
        __(ret)
local_label(misc_ref_s8):
	__(ldrsb arg_z,[arg_y,arg_z])
	__(ret)
local_label(misc_ref_u8):
	__(ldrb gpr32(arg_z),[arg_y,arg_z])
	__(ret)
local_label(misc_ref_u16):
	__(ldrh gpr32(arg_z),[arg_y,arg_z,lsl #1])
	__(ret)
local_label(misc_ref_s16):
	__(ldrsh arg_z,[arg_y,arg_z,lsl #1])
	__(ret)
                
local_label(misc_ref_invalid):
	__(mov arg_x,#XBADVEC)
	__(set_nargs(3))
	__(b _SPksignalerr)        
_endfn
        
_startfn(C(misc_set_common))
        /* imm1 = header subtag (high byte of header word, uvector_header-based) */
        __(and imm0,imm1,#uvector_mask)
        __(cmp imm0,#uvector_header)
        __(bne local_label(misc_set_invalid))
        __(tst imm1,#gvector_tag_mask)
        __(beq 0f)
        __(cmp imm1,#subtag_function)
        __(bne _SPgvset)
        __(getvheader(imm0,arg_y,imm0))
        __(sub imm0,imm0,#1)
        __(ldr imm0,[arg_y,imm0,lsl #3])
        __(cmp arg_z,imm0)
        __(blo local_label(misc_set_u64))
        __(b _SPgvset)
0:      __(and imm1,imm1,#31)
        __(adr imm0,local_label(misc_set_jmp))
        __(add imm0,imm0,imm1,lsl #2)
        __(br imm0)        

/* Jump table indexed by type_bits & 0x1F (lower 5 bits of header subtag).
   ARM64 TBI ivector type_bits layout:
     define_ivector(name, n) -> type_bits = n*2 (even)
     define_cl_ivector(name, n) -> type_bits = n*2|1 (odd)  */
local_label(misc_set_jmp):
        __(b local_label(misc_set_u32))                  /* 0: bignum */
        __(b local_label(misc_set_s32))                  /* 1: s32_vector */
        __(b local_label(misc_set_u32))                  /* 2: double_float */
        __(b local_label(misc_set_u32))                  /* 3: u32_vector */
        __(b local_label(misc_set_u32))                  /* 4: complex_single_float */
        __(b local_label(misc_set_single_float_vector))  /* 5: single_float_vector */
        __(b local_label(misc_set_u32))                  /* 6: complex_double_float */
        __(b local_label(misc_set_simple_string))        /* 7: simple_string */
        __(b local_label(misc_set_u32))                  /* 8: xcode_vector */
        __(b local_label(misc_set_invalid))              /* 9: (unused) */
        __(b local_label(misc_set_u64))                  /* 10: macptr */
        __(b local_label(misc_set_s64))                  /* 11: s64_vector */
        __(b local_label(misc_set_u64))                  /* 12: dead_macptr */
        __(b local_label(misc_set_u64))                  /* 13: u64_vector */
        __(b local_label(misc_set_invalid))              /* 14: (unused) */
        __(b local_label(misc_set_fixnum))               /* 15: fixnum_vector */
        __(b local_label(misc_set_invalid))              /* 16: (unused) */
        __(b local_label(misc_set_double_float_vector))  /* 17: double_float_vector */
        __(b local_label(misc_set_invalid))              /* 18: (unused) */
        __(b local_label(misc_set_u64))                  /* 19: complex_sf_vector */
        __(b local_label(misc_set_invalid))              /* 20: (unused) */
        __(b local_label(misc_set_s8))                   /* 21: s8_vector */
        __(b local_label(misc_set_invalid))              /* 22: (unused) */
        __(b local_label(misc_set_u8))                   /* 23: u8_vector */
        __(b local_label(misc_set_invalid))              /* 24: (unused) */
        __(b local_label(misc_set_s16))                  /* 25: s16_vector */
        __(b local_label(misc_set_invalid))              /* 26: (unused) */
        __(b local_label(misc_set_u16))                  /* 27: u16_vector */
        __(b local_label(misc_set_invalid))              /* 28: (unused) */
        __(b local_label(misc_set_u64))                  /* 29: complex_df_vector */
        __(b local_label(misc_set_invalid))              /* 30: (unused) */
        __(b local_label(misc_set_bit_vector))           /* 31: bit_vector */

local_label(misc_set_u32):
        __(extract_unsigned_byte(imm0,arg_z,32))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
local_label(set_set32):         
	__(str gpr32(arg_z),[arg_x,arg_y,lsl #2])
	__(ret)
local_label(set_bad):
	/* arg_z does not match the array-element-type of arg_x.  */
	__(mov arg_y,arg_z)
	__(mov arg_z,arg_x)
	__(mov arg_x,#XNOTELT)
	__(set_nargs(3))
	__(b _SPksignalerr)
local_label(misc_set_fixnum):
        __(extract_signed_byte(imm0,arg_z,56))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
local_label(misc_set_64):               
        __(str arg_z,[arg_x,arg_y,lsl #word_shift])
        __(ret)
local_label(misc_set_simple_string):
        __(extract_tag(imm0,arg_z))
        __(cmp imm0,#tag_character)
        __(bne local_label(set_bad))
        __(lsr imm0,arg_z,#charcode_shift)
        __(str gpr32(imm0),[arg_x,arg_y,lsl #2])
	__(ret)
local_label(misc_set_s32):
        __(extract_signed_byte(imm0,arg_z,32))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
        __(str gpr32(arg_z),[arg_x,arg_y,lsl #2])
        __(ret)
local_label(misc_set_single_float_vector):
        __(extract_tag(imm0,arg_z))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
        __(str gpr32(arg_z),[arg_x,arg_y,lsl #2])
        __(ret)
local_label(misc_set_u8):
        __(extract_unsigned_byte(imm0,arg_z,8))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
        __(strb gpr32(arg_z),[arg_x,arg_y])
        __(ret)
local_label(misc_set_s8):
        __(extract_signed_byte(imm0,arg_z,8))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
        __(strb gpr32(arg_z),[arg_x,arg_y])
        __(ret)
local_label(misc_set_u16):
        __(extract_unsigned_byte(imm0,arg_z,16))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
        __(strh gpr32(arg_z),[arg_x,arg_y,lsl #1])
        __(ret)
local_label(misc_set_s16):
        __(extract_signed_byte(imm0,arg_z,16))
        __(cmp imm0,arg_z)
        __(bne local_label(set_bad))
        __(strh gpr32(arg_z),[arg_x,arg_y,lsl #1])
        __(ret)
local_label(misc_set_bit_vector):
        __(mov imm1,#1)
        __(cmp arg_z,imm1)
        __(bhi local_label(set_bad))
        __(and temp0,arg_y,#63)
        __(eor temp0,temp0,#63)
        __(lsl imm1,imm1,temp0)
        __(lsl imm0,arg_z,temp0)
        __(lsr temp1,arg_y,#6)
        __(ldr imm2,[arg_x,temp1,lsl #word_shift])
        __(bic imm2,imm2,imm1)
        __(orr imm2,imm2,imm0)
        __(str imm2,[arg_x,temp1,lsl #word_shift])
        __(ret)
local_label(misc_set_s64):
        __(extract_signed_byte(imm0,arg_z,56))
        __(cmp imm0,arg_z)
        __(beq local_label(misc_set_64))
        __(extract_tag(imm0,arg_z))
        __(cmp imm0,#tag_bignum)
        __(bne local_label(set_bad))
        __(vector_length(imm0,arg_z,imm0))
        __(cmp imm0,#2)
        __(bne local_label(set_bad))
        __(ldr imm0,[arg_z,#0])
        __(str imm0,[arg_x,arg_y,lsl #word_shift])
        __(ret)
local_label(misc_set_u64):
        __(extract_unsigned_byte(imm0,arg_z,56))
        __(cmp imm0,arg_z)
        __(beq local_label(misc_set_64))
        __(extract_tag(imm0,arg_z))
        __(cmp imm0,#tag_bignum)
        __(bne local_label(set_bad))
        __(vector_length(imm0,arg_z,imm0))
        __(cmp imm0,#2)
        __(bne local_label(local_label_misc_set_u64_3_digit))
        __(ldr imm0,[arg_z,#0])
        __(branch_if_negative(imm0,local_label(set_bad)))
        __(str imm0,[arg_x,arg_y,lsl #word_shift])
        __(ret)
local_label(local_label_misc_set_u64_3_digit):  
        __(cmp imm0,#3)
        __(bne local_label(set_bad))
        __(ldr gpr32(imm0),[arg_z,#2<<2])
        __(cbnz imm0,local_label(set_bad))
        __(ldr imm0,[arg_z,#0])
        __(str imm0,[arg_x,arg_y,lsl #word_shift])
        __(ret)
local_label(misc_set_double_float_vector):
	__(extract_tag(imm0,arg_z))
	__(cmp imm0,#tag_double_float)
	__(bne local_label(set_bad))
        __(ldr imm0,[arg_z,#0])
        __(str imm0,[arg_x,arg_y,lsl #word_shift])
	__(ret)
local_label(misc_set_invalid):  
	__(mov temp0,#XSETBADVEC)        
	__(set_nargs(4))
	__(vpush1(temp0))
	__(b _SPksignalerr)                

        
/* temp0: (stack-consed) target catch frame, imm0: count of intervening  */
/* frames. If target isn't a multiple-value receiver, discard extra values */
/* (less hair, maybe.)  */
_startfn(C(_throw_found))
        new_local_labels()
        __(ldr imm1,[temp0,#catch_frame.mvflag])
        __(cmp imm1,#0)
        __(add imm1,vsp,nargs)
        __(add imm1,imm1,#-node_size)
        __(bne local_label(throw_all_values))
        __(cmp nargs,#0)
        __(bne 0f)
        __(mov imm1,rnil)
        __(set_nargs(1))
        __(str imm1,[vsp,#-node_size]!)
        __(b local_label(throw_all_values))
0:
        __(set_nargs(1))
        __(mov vsp,imm1)
local_label(throw_all_values):  
        __(bl _SPnthrowvalues) 
        __(ldr temp0,[rcontext,#tcr.catch_top])
        __(ldr imm1,[rcontext,#tcr.db_link])
        __(ldr imm0,[temp0,#catch_frame.db_link])
        __(cmp imm0,imm1)
        __(beq 0f)
        __(bl _SPunbind_to)
0:
        __(ldr temp1,[temp0,#catch_frame.mvflag])
        __(ldr imm0,[temp0,#catch_frame.xframe])
        __(ldr imm1,[temp0,#catch_frame.last_lisp_frame])
        __(cmp temp1,#0)
        __(str imm0,[rcontext,#tcr.xframe])
        __(str imm1,[rcontext,#tcr.last_lisp_frame])
        __(add imm2,vsp,nargs)
        __(ubfx imm0,temp0,#0,#56)
        __(sub imm0,imm0,#node_size)  /* back to header = 16-byte aligned */
        __(mov sp,imm0)
        __(ldr imm1,[sp,#catch_frame_alloc+lisp_frame.savevsp])
        __(bne local_label(throw_push_test_entry))
        __(ldr arg_z,[imm2,#-node_size])
        __(b local_label(throw_pushed_values))
local_label(throw_push_test_entry):
        __(mov arg_x,nargs)
        __(b local_label(throw_push_test))
local_label(throw_push_loop):
        __(sub arg_x,arg_x,#fixnumone)
        __(ldr arg_y,[imm2,#-node_size]!)
        __(push1(arg_y,imm1))
local_label(throw_push_test):
        __(cbnz  arg_x,local_label(throw_push_loop))
local_label(throw_pushed_values):
        __(mov vsp,imm1)
        __(ldr imm0,[temp0,#catch_frame.link])
        __(str imm0,[rcontext,#tcr.catch_top])
        __(ldr lr,[sp,#catch_frame_alloc+lisp_frame.savelr])
        __(ldp nfn,x29,[sp,#catch_frame_alloc+lisp_frame.savefn])
        __(add sp,sp,#catch_frame_alloc+lisp_frame.size)
        __(pop_lisp_fprs())
        __(ret)
_endfn(C(_throw_found))        

_startfn(C(nthrow1v))
        new_local_labels()
        /* Bug 167: save lr to global — throw processing may corrupt lr */
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(str lr,[imm0,_nthrow_saved_lr@PAGEOFF])
local_label(_nthrow1v_nextframe):
        __(subs temp2,temp2,#fixnum_one)
        __(ldr temp0,[rcontext,#tcr.catch_top])
        __(ldr imm1,[rcontext,#tcr.db_link])
        __(set_nargs(1))
        __(blt local_label(_nthrow1v_done))
        __(cbz temp0,local_label(_nthrow1v_no_catch))
        __(ldr arg_y,[temp0,#catch_frame.link])
        __(ldr imm0,[temp0,#catch_frame.db_link])
        __(cmp imm0,imm1)
        __(str arg_y,[rcontext,#tcr.catch_top])
        __(ldr arg_y,[temp0,#catch_frame.xframe])
        __(str arg_y,[rcontext,#tcr.xframe])
        __(beq local_label(_nthrow1v_dont_unbind))
        __(do_unbind_to(imm1,temp1,arg_x,arg_y))
local_label(_nthrow1v_dont_unbind):
        __(ldr temp1,[temp0,#catch_frame.catch_tag])
        __(cmp_tag_to_marker(temp1,imm1,tag_unbound))  /* unwind-protect ?  */
        __(ubfx imm0,temp0,#0,#56)
        __(sub imm0,imm0,#node_size)  /* back to header = stack allocation point */
        __(mov sp,imm0)
        __(beq local_label(_nthrow1v_do_unwind))
        /* A catch frame.  If the last one, restore context from there.  */
        __(cbnz temp2,0f)
        __(ldr vsp,[sp,#catch_frame_alloc+lisp_frame.savevsp])
0:
        __(ldr x29,[sp,#catch_frame_alloc+lisp_frame.savefp])
        __(add sp,sp,#catch_frame_alloc+lisp_frame.size)
        __(pop_lisp_fprs())
        __(b local_label(_nthrow1v_nextframe))
local_label(_nthrow1v_do_unwind):
        /* This is harder, but not as hard (not as much BLTing) as the  */
        /* multiple-value case.  */
        /* Save our caller's LR and FN in the csp frame created by the unwind-  */
        /* protect.  (Clever, eh ?)  */
        __(add sp,sp,#catch_frame_alloc)
        /* We used to use a swp instruction to exchange the lr with
        the lisp_frame.savelr field of the lisp frame that temp0 addresses.
        Multicore ARMv7 machines include the ability to disable the swp
        instruction, and some Linux kernels do so and emulate the instruction.
        There seems to be evidence that they sometimes do so incorrectly,
        so we stopped using swp.
        pc_luser_xp() needs to do some extra work if the thread is interrupted
        in the midst of the three-instruction sequence at
	swap_lr_lisp_frame_temp0.
        */
        __(mov imm1,#0)
        __(mov temp0,sp)
        __(movz imm0,#3)
        __(movk imm0,#(subtag_simple_vector << 8),lsl #48)
        __(stp imm0,imm1,[sp,#-4*node_size]!)
        __(stp arg_z,temp2,[sp,#2*node_size])
        .globl C(swap_lr_lisp_frame_temp0)
        .globl C(swap_lr_lisp_frame_temp0_end)
        /* This instruction sequence needs support from pc_luser_xp() */
C(swap_lr_lisp_frame_temp0):
        __(ldr imm0,[temp0,#lisp_frame.savelr])
        __(str lr,[temp0,#lisp_frame.savelr])
        __(mov lr,imm0)
C(swap_lr_lisp_frame_temp0_end):
        __(ldp nfn,x29,[temp0,#lisp_frame.savefn])
        __(str fn,[temp0,#lisp_frame.savefn])
        __(ldr vsp,[temp0,#lisp_frame.savevsp])
        __(add temp0,temp0,#lisp_frame.size)
        __(restore_lisp_fprs(temp0))
        __(str imm1,[rcontext,#tcr.unwinding])
        /* Bug 170: save sp and nthrow_saved_lr to TCR spare slots
           across cleanup call (same approach as nthrownv). */
        __(mov imm0,sp)
        __(str imm0,[rcontext,#tcr_nthrow_sp])
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(ldr imm0,[imm0,_nthrow_saved_lr@PAGEOFF])
        __(str imm0,[rcontext,#tcr_nthrow_lr])
        __(blr lr)
        __(ldr imm0,[rcontext,#tcr_nthrow_sp])
        __(mov sp,imm0)
        __(ldr imm1,[rcontext,#tcr_nthrow_lr])
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(str imm1,[imm0,_nthrow_saved_lr@PAGEOFF])
        __(mov imm1,#1)
        __(ldr arg_z,[sp,#2*node_size])
        __(str imm1,[rcontext,#tcr.unwinding])
        /* Bug 151: temp2=nfn=x10 on ARM64.  restore_lisp_frame() loads
           nfn into x10, then mov temp2,imm0 would clobber it with the
           throw count.  Since the throw loop only needs the count in
           temp2 (and each unwind-protect loads its own nfn from its
           frame), skip the nfn restore entirely. */
        __(ldr temp2,[sp,#3*node_size])
        __(add sp,sp,#4*node_size)
        __(ldr x29,[sp,#lisp_frame.savefp])
        __(ldp vsp,lr,[sp],#lisp_frame.size)
        __(discard_lisp_fprs())
        __(b local_label(_nthrow1v_nextframe))
local_label(_nthrow1v_no_catch):
        __(hlt #0xFFFC)
local_label(_nthrow1v_done):
        __(mov imm0,#0)
        __(str imm0,[rcontext,#tcr.unwinding])
        /* Bug 167/168: gap-skipping moved to per-frame (same as nthrownv) */
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(ldr lr,[imm0,_nthrow_saved_lr@PAGEOFF])
        __(check_pending_interrupt(nargs))
        __(ret)
_endfn

_startfn(C(nthrownv))
        new_local_labels()
        /* Bug 167: save lr to global — throw processing may corrupt lr */
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(str lr,[imm0,_nthrow_saved_lr@PAGEOFF])
local_label(nthrownv_nextframe):
        __(subs temp2,temp2,#fixnum_one)
        __(ldr temp0,[rcontext,#tcr.catch_top])
        __(ldr imm1,[rcontext,#tcr.db_link])
        __(blt local_label(nthrownv_done))
        __(cbz temp0,local_label(nthrownv_no_catch))
        __(ldr arg_y,[temp0,#catch_frame.link])
        __(ldr imm0,[temp0,#catch_frame.db_link])
        __(cmp imm0,imm1)
        __(str arg_y,[rcontext,#tcr.catch_top])
        __(ldr arg_y,[temp0,#catch_frame.xframe])
        __(str arg_y,[rcontext,#tcr.xframe])
        __(beq local_label(nthrownv_dont_unbind))
        __(do_unbind_to(imm1,temp1,arg_x,arg_y))
local_label(nthrownv_dont_unbind):
        __(ldr temp1,[temp0,#catch_frame.catch_tag])
        __(cmp_tag_to_marker(temp1,imm1,tag_unbound))  /* unwind-protect ?  */
        __(ubfx imm0,temp0,#0,#56)
        __(sub imm0,imm0,#node_size)  /* back to header = 16-byte aligned */
        __(mov sp,imm0)
        __(beq local_label(nthrownv_do_unwind))
        __(cmp temp2,#0)
/* A catch frame.  If the last one, restore context from there.  */
	__(bne local_label(nthrownv_skip))
        __(ldr imm0,[sp,#catch_frame_alloc+lisp_frame.savevsp])
        __(add imm1,vsp,nargs)
        __(mov arg_z,nargs)
        __(b local_label(nthrownv_push_test))
local_label(nthrownv_push_loop):
        __(sub arg_z,arg_z,#fixnumone)
        __(ldr temp1,[imm1,#-node_size]!)
        __(push1(temp1,imm0))
local_label(nthrownv_push_test):
        __(cbnz arg_z,local_label(nthrownv_push_loop))
        __(mov vsp,imm0)
local_label(nthrownv_skip):
        __(ldr x29,[sp,#catch_frame_alloc+lisp_frame.savefp])
        __(add sp,sp,#catch_frame_alloc+lisp_frame.size)
        __(pop_lisp_fprs())
        __(b local_label(nthrownv_nextframe))                
local_label(nthrownv_do_unwind):
        __(ldr arg_x,[temp0,#catch_frame.xframe])
        __(ldr arg_z,[temp0,#catch_frame.last_lisp_frame])
        __(ubfx imm0,temp0,#0,#56)
        __(sub imm0,imm0,#node_size)  /* back to header = 16-byte aligned */
        __(mov sp,imm0)
        __(str arg_x,[rcontext,#tcr.xframe])
        __(str arg_z,[rcontext,#tcr.last_lisp_frame])
        __(add sp,sp,#catch_frame_alloc)
        __(add imm1,nargs,#node_size)
        __(mov arg_z,sp)
        __(dnode_align(imm0,imm1,node_size))
        __(movk imm1,#(subtag_simple_vector << 8),lsl #48)
        __(stack_allocate_zeroed_ivector(imm1,imm0))
        __(str temp2,[sp,#node_size])
        __(add temp2,sp,#dnode_size)
        __(add temp2,temp2,nargs)
        __(add temp1,vsp,nargs)
        __(b local_label(nthrownv_tpushtest))
local_label(nthrownv_tpushloop):        
        __(ldr temp0,[temp1,#-node_size]!)
        __(push1(temp0,temp2))
local_label(nthrownv_tpushtest):        
        __(subs nargs,nargs,#node_size)
        __(bge local_label(nthrownv_tpushloop))
        __(mov imm1,#0)
        /* This instruction sequence needs support from pc_luser_xp() */
        .globl C(swap_lr_lisp_frame_arg_z)
        .globl C(swap_lr_lisp_frame_arg_z_end)
C(swap_lr_lisp_frame_arg_z):                   
        __(ldr imm0,[arg_z,#lisp_frame.savelr])
        __(str lr,[arg_z,#lisp_frame.savelr])
        __(mov lr,imm0)
C(swap_lr_lisp_frame_arg_z_end):
        __(ldp nfn,x29,[arg_z,#lisp_frame.savefn])
        __(str fn,[arg_z,#lisp_frame.savefn])
        __(ldr vsp,[arg_z,#lisp_frame.savevsp])
        __(add arg_z,arg_z,#lisp_frame.size)
        __(restore_lisp_fprs(arg_z))
        __(str imm1,[rcontext,#tcr.unwinding])
        /* Bug 170: save sp to TCR spare slot across cleanup call.
           Neither save registers nor global variables survive cleanup:
           save0/x16 clobbered by linker (Bug 169), save3/x19 clobbered
           by Lisp code (Bug 170), globals zeroed (Bug 170).
           TCR spare slot at offset 0x160 is untouched by any code path.
           Also save nthrow_saved_lr to TCR spare[1] so nested throws
           inside cleanup don't overwrite the outer nthrownv's entry lr. */
        __(mov imm0,sp)
        __(str imm0,[rcontext,#tcr_nthrow_sp])
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(ldr imm0,[imm0,_nthrow_saved_lr@PAGEOFF])
        __(str imm0,[rcontext,#tcr_nthrow_lr])
        __(blr lr)
        /* Bug 170: restore sp and nthrow_saved_lr from TCR spare slots */
        __(ldr imm0,[rcontext,#tcr_nthrow_sp])
        __(mov sp,imm0)
        __(ldr imm1,[rcontext,#tcr_nthrow_lr])
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(str imm1,[imm0,_nthrow_saved_lr@PAGEOFF])
        __(mov imm1,#1)
        __(str imm1,[rcontext,#tcr.unwinding])
        __(ldr imm0,[sp])
        __(header_length(imm0,imm0))
        __(subs nargs,imm0,#node_size)
        /* Bug 166: if nargs <= 0, skip the value restore loop entirely.
           When the saved-values header has 0 count, nargs = -8 and the
           loop would run forever, overflowing the vstack. */
        __(ble local_label(nthrownv_tpop_done))
        __(add imm0,imm0,#node_size)
        __(add temp0,sp,imm0)
        __(mov imm0,nargs)
        __(add arg_z,temp0,#node_size)
        /* Bug 170: fulltagmask=0xff on ARM64 (TBI tag in high byte).
           Using bic with fulltagmask strips 8 low bits of the raw stack
           address, corrupting it by up to 255 bytes.  Use dnode_size-1
           instead for proper 16-byte alignment. */
        __(bic arg_z,arg_z,#(dnode_size-1))
        __(b local_label(nthrownv_tpoptest))
local_label(nthrownv_tpoploop):
        __(subs imm0,imm0,#node_size)
        __(vpush1(temp2))
local_label(nthrownv_tpoptest):
        __(ldr temp2,[temp0,#-node_size]!)
        __(bne local_label(nthrownv_tpoploop))
local_label(nthrownv_tpop_done):
        /* Bug 151: fn=nfn=temp2=x10 on ARM64.  The old code saved temp2
           to imm0, loaded fn (clobbering x10), then restored temp2 from
           imm0 (clobbering fn).  Skip the pointless fn load; temp2
           already holds the throw count we need. */
        __(mov sp,arg_z)
        __(ldr lr,[sp,#lisp_frame.savelr])
        __(discard_lisp_frame())
        __(discard_lisp_fprs())
        __(b local_label(nthrownv_nextframe))
local_label(nthrownv_no_catch):
        /* catch_top is NULL but frames remain — fatal error */
        __(hlt #0xFFFC)
local_label(nthrownv_done):
        __(mov imm0,#0)
        __(str imm0,[rcontext,#tcr.unwinding])
        /* Bug 167/168: The gap-skipping `mov sp,x29` was moved to
           nthrownv_skip (per catch frame pop) because doing it here
           at nthrownv_done corrupted sp when nthrownv was called
           recursively from an unwind-protect cleanup function.
           sp should now already be correct from the per-frame skip. */
        __(adrp imm0,_nthrow_saved_lr@PAGE)
        __(ldr lr,[imm0,_nthrow_saved_lr@PAGEOFF])
        __(check_pending_interrupt(imm1))
        __(ret)
_endfn


_startfn(stack_misc_alloc_init_no_room)
/* Too large to safely fit on tstack.  Heap-cons the vector, but make  */
/* sure that there's an empty tsp frame to keep the compiler happy.  */
        __(load_marker(imm0,tag_stack_alloc))
        __(mov imm1,sp)
        __(stp imm0,imm1,[sp,#-dnode_size]!)
        __(b _SPmisc_alloc_init)
_endfn        
_startfn(stack_misc_alloc_init_ivector)
        __(lsl imm0,arg_y,#subtag_shift)
        __(orr imm0,imm0,arg_x)
        /* Compute byte count from element count (arg_x) and subtag (arg_y).
           On ARM64 with fixnumshift=0, arg_x IS the element count.
           Subtag order: 32-bit(≤0x88) 64-bit(≤0x93) 8-bit(≤0x97) 16-bit(≤0x9B) 128-bit(0x9D) bit(0x9F) */
        __(cmp arg_y,#max_32_bit_ivector_subtag)
        __(bgt 1f)
        __(lsl imm1,arg_x,#2)  /* 32-bit elements: count * 4 */
        __(b 8f)
1:      __(cmp arg_y,#max_64_bit_ivector_subtag)
        __(bgt 2f)
        __(lsl imm1,arg_x,#3)  /* 64-bit elements: count * 8 */
        __(b 8f)
2:      __(cmp arg_y,#max_8_bit_ivector_subtag)
        __(bgt 3f)
        __(mov imm1,arg_x)  /* 8-bit elements: count bytes */
        __(b 8f)
3:      __(cmp arg_y,#max_16_bit_ivector_subtag)
        __(bgt 4f)
        __(lsl imm1,arg_x,#1)  /* 16-bit elements: count * 2 */
        __(b 8f)
4:      __(cmp arg_y,#subtag_complex_double_float_vector)
        __(bne 5f)
        __(lsl imm1,arg_x,#4)  /* 128-bit: count * 16 */
        __(b 8f)
5:      __(add imm1,arg_x,#7)  /* bit vector: (count+7)/8 */
        __(lsr imm1,imm1,#3)
8:      __(dnode_align(imm1,imm1,node_size))
        __(ldr temp0,[rcontext,#tcr.cs_limit])
        __(sub temp1,sp,imm1)
        __(cmp temp1,temp0)
        __(bls stack_misc_alloc_init_no_room)
        __(load_marker(temp0,tag_stack_alloc))
        __(mov temp1,sp)
        __(stack_allocate_zeroed_ivector(imm0,imm1))
        __(mov arg_y,arg_z)
        __(add arg_z,sp,#node_size)
        __(orr arg_z,arg_z,#(fulltag_misc << tag_shift))
        __(stp temp0,temp1,[sp,#-dnode_size]!)
        __(b initialize_vector)
_endfn
/* This is called from a lisp-style context and calls a lisp function. */
/* This does the moral equivalent of */
/*   (loop  */
/*	(let* ((fn (%function_on_top_of_lisp_stack))) */
/*	  (if fn */
/*           (catch %toplevel-catch% */
/*	       (funcall fn)) */
/*            (return nil)))) */

_startfn(toplevel_loop)
        __(build_lisp_frame())
	__(b local_label(test))
local_label(loop):
	__(ref_nrs_value(arg_z,toplcatch))
	__(bl _SPmkcatch1v)
	__(b local_label(test))	/* cleanup address, not really a branch */
        __(ldr nfn,[vsp,#0])
	__(set_nargs(0))
        __(bl _SPfuncall)
	__(mov arg_z,rnil)
	__(mov imm0,#fixnum_one)
	__(bl _SPnthrow1value)
local_label(test):
        __(ldr nfn,[vsp,#0])
        __(cmp nfn,rnil)
	__(bne local_label(loop))
        __(return_lisp_frame())
	_endfn


/* This gets called with R0 pointing to the current TCR. */
/* r1 is 0 if we want to start the whole thing rolling, */
/* non-zero if we want to reset the current process */
/* by throwing to toplevel */

	.globl _SPreset
_exportfn(C(start_lisp))
        /* Save callee-saved registers (AAPCS64: x19-x28, x29, x30) */
        __(stp x29,x30,[sp,#-16*7]!)
        __(stp x19,x20,[sp,#16])
        __(stp x21,x22,[sp,#32])
        __(stp x23,x24,[sp,#48])
        __(stp x25,x26,[sp,#64])
        __(stp x27,x28,[sp,#80])
        __(mov x29,sp)
        __(str x29,[sp,#96])  /* save original sp */
        /* x0 = tcr, x1 = reset flag */
        __(mov rcontext,x0)
        /* SP is already 16-byte aligned on ARM64 */
        __(mov arg_z,#0)
        __(mov arg_y,#0)
        __(mov arg_x,#0)
        __(mov temp0,#0)
        __(mov temp1,#0)
        __(mov temp2,#0)
        __(load_nil(rnil))
        __(load_t(rt,rnil))
        __(load_voidptr(allocptr))
        __(ldr vsp,[rcontext,#tcr.save_vsp])
        __(ldr imm2,[rcontext,#tcr.last_lisp_frame])
        __(mov imm0,sp)
        __(sub imm0,imm2,imm0)
        __(add imm0,imm0,#node_size)
        __(lsr imm0,imm0,#word_shift)
        __(movk imm0,#(subtag_u64_vector << 8),lsl #48)
        __(stp imm0,imm2,[sp,#-dnode_size]!)
        __(push_foreign_fprs())
        /* Zero double_float_zero (d15) */
        __(fmov double_float_zero,xzr)
        __(mov imm0,#TCR_STATE_LISP)
        __(str imm0,[rcontext,#tcr.valence])
        __(ldr allocptr,[rcontext,#tcr.save_allocptr])
        __(ldr allocbase,[rcontext,#tcr.save_allocbase])
        __(bl toplevel_loop)
        __(ldr imm1,[sp,#(10*8)+node_size]) /* past FPR vector + header */
        __(mov imm0,#TCR_STATE_FOREIGN)
        __(str imm1,[rcontext,#tcr.last_lisp_frame])
        __(str imm0,[rcontext,#tcr.valence])
        __(pop_foreign_fprs())
        __(add sp,sp,#2*node_size)
        __(mov imm0,rnil)
        /* Restore callee-saved registers */
        __(mov sp,x29)
        __(ldp x19,x20,[sp,#16])
        __(ldp x21,x22,[sp,#32])
        __(ldp x23,x24,[sp,#48])
        __(ldp x25,x26,[sp,#64])
        __(ldp x27,x28,[sp,#80])
        __(ldp x29,x30,[sp],#16*7)
        __(ret)
_endfn

/* This gets called with r0 = the current thread's TCR.  Should
   call RESTORE-LISP-POINTERS and return 0 if it returns normally
   and non-0 if it throws. */
        
_exportfn(C(init_lisp))
        new_local_labels()
        new_macro_labels()
        /* Save callee-saved registers (AAPCS64: x19-x28, x29, x30) */
        __(stp x29,x30,[sp,#-16*7]!)
        __(stp x19,x20,[sp,#16])
        __(stp x21,x22,[sp,#32])
        __(stp x23,x24,[sp,#48])
        __(stp x25,x26,[sp,#64])
        __(stp x27,x28,[sp,#80])
        __(mov x29,sp)
        __(str x29,[sp,#96])
        __(mov rcontext,x0)
        __(mov arg_z,#0)
        __(mov arg_y,#0)
        __(mov arg_x,#0)
        __(mov temp0,#0)
        __(mov temp1,#0)
        __(mov temp2,#0)
        __(load_nil(rnil))
        __(load_t(rt,rnil))
        __(load_voidptr(allocptr))
        __(ldr vsp,[rcontext,#tcr.save_vsp])
        __(ldr imm2,[rcontext,#tcr.last_lisp_frame])
        __(mov imm0,sp)
        __(sub imm0,imm2,imm0)
        __(add imm0,imm0,#node_size)
        __(lsr imm0,imm0,#word_shift)
        __(movk imm0,#(subtag_u64_vector << 8),lsl #48)
        __(stp imm0,imm2,[sp,#-dnode_size]!)
        __(push_foreign_fprs())
        __(fmov double_float_zero,xzr)
        __(mov imm0,#TCR_STATE_LISP)
        __(str imm0,[rcontext,#tcr.valence])
        __(ldr allocptr,[rcontext,#tcr.save_allocptr])
        __(ref_nrs_function(nfn,restore_lisp_pointers))
        __(extract_subtag(imm0,nfn))
        __(cmp imm0,#subtag_function)
        __(bne local_label(fail))
        __(ref_nrs_value(arg_z,toplcatch))
        __(bl _SPmkcatch1v)
        __(b local_label(fail)) /* cleanup address */
        __(ref_nrs_function(nfn,restore_lisp_pointers))
        __(set_nargs(0))
        __(bl _SPfuncall)
        __(mov arg_z,#0)
        __(mov imm0,#fixnum_one)
        __(bl _SPnthrow1value)
        __(b local_label(done))
local_label(fail):
        __(mov arg_z,#fixnum_one)
local_label(done):
        __(ldr imm1,[sp,#(10*8)+node_size])
        __(mov imm0,#TCR_STATE_FOREIGN)
        __(str imm1,[rcontext,#tcr.last_lisp_frame])
        __(str imm0,[rcontext,#tcr.valence])
        __(pop_foreign_fprs())
        __(add sp,sp,#2*node_size)
        __(unbox_fixnum(imm0,arg_z))
        /* Restore callee-saved registers */
        __(mov sp,x29)
        __(ldp x19,x20,[sp,#16])
        __(ldp x21,x22,[sp,#32])
        __(ldp x23,x24,[sp,#48])
        __(ldp x25,x26,[sp,#64])
        __(ldp x27,x28,[sp,#80])
        __(ldp x29,x30,[sp],#16*7)
        __(ret)
_endfn

                                
        .data
        .globl C(sptab)
        .globl C(sptab_end)
        new_local_labels()
C(sptab):
        .quad local_label(start)
C(sptab_end):   
        .quad local_label(end)
local_label(start):                     
        .quad _SPfix_nfn_entrypoint /* must be first */
        .quad _SPbuiltin_plus
        .quad _SPbuiltin_minus
        .quad _SPbuiltin_times
        .quad _SPbuiltin_div
        .quad _SPbuiltin_eq
        .quad _SPbuiltin_ne
        .quad _SPbuiltin_gt
        .quad _SPbuiltin_ge
        .quad _SPbuiltin_lt
        .quad _SPbuiltin_le
        .quad _SPbuiltin_eql
        .quad _SPbuiltin_length
        .quad _SPbuiltin_seqtype
        .quad _SPbuiltin_assq
        .quad _SPbuiltin_memq
        .quad _SPbuiltin_logbitp
        .quad _SPbuiltin_logior
        .quad _SPbuiltin_logand
        .quad _SPbuiltin_ash
        .quad _SPbuiltin_negate
        .quad _SPbuiltin_logxor
        .quad _SPbuiltin_aref1
        .quad _SPbuiltin_aset1
        .quad _SPfuncall
        .quad _SPmkcatch1v
        .quad _SPmkcatchmv
        .quad _SPmkunwind
        .quad _SPbind
        .quad _SPconslist
        .quad _SPconslist_star
        .quad _SPmakes32
        .quad _SPmakeu32
        .quad _SPfix_overflow
        .quad _SPmakeu64
        .quad _SPmakes64
        .quad _SPmvpass
        .quad _SPvalues
        .quad _SPnvalret
        .quad _SPthrow
        .quad _SPnthrowvalues
        .quad _SPnthrow1value
        .quad _SPbind_self
        .quad _SPbind_nil
        .quad _SPbind_self_boundp_check
        .quad _SPrplaca
        .quad _SPrplacd
        .quad _SPgvset
        .quad _SPset_hash_key
        .quad _SPstore_node_conditional
        .quad _SPset_hash_key_conditional
        .quad _SPstkconslist
        .quad _SPstkconslist_star
        .quad _SPmkstackv
        .quad _SPsetqsym
        .quad _SPprogvsave
        .quad _SPstack_misc_alloc
        .quad _SPgvector
        .quad _SPfitvals
        .quad _SPnthvalue
        .quad _SPdefault_optional_args
        .quad _SPopt_supplied_p
        .quad _SPheap_rest_arg
        .quad _SPreq_heap_rest_arg
        .quad _SPheap_cons_rest_arg
        .quad _SPcheck_fpu_exception
        .quad _SPdiscard_stack_object
        .quad _SPksignalerr
        .quad _SPstack_rest_arg
        .quad _SPreq_stack_rest_arg
        .quad _SPstack_cons_rest_arg
        .quad _SPcall_closure        
        .quad _SPspreadargz
        .quad _SPtfuncallgen
        .quad _SPtfuncallslide
        .quad _SPjmpsym
        .quad _SPtcallsymgen
        .quad _SPtcallsymslide
        .quad _SPtcallnfngen
        .quad _SPtcallnfnslide
        .quad _SPmisc_ref
        .quad _SPsubtag_misc_ref
        .quad _SPmakestackblock
        .quad _SPmakestackblock0
        .quad _SPmakestacklist
        .quad _SPstkgvector
        .quad _SPmisc_alloc
        .quad _SPatomic_incf_node
        .quad _SPunused1
        .quad _SPunused2
        .quad _SPrecover_values
        .quad _SPinteger_sign
        .quad _SPsubtag_misc_set
        .quad _SPmisc_set
        .quad _SPspread_lexprz
        .quad _SPreset
        .quad _SPmvslide
        .quad _SPsave_values
        .quad _SPadd_values
        .quad _SPmisc_alloc_init
        .quad _SPstack_misc_alloc_init
        .quad _SPpopj
        .quad _SPudiv64by32
        .quad _SPgetu64
        .quad _SPgets64
        .quad _SPspecref
        .quad _SPspecrefcheck
        .quad _SPspecset
        .quad _SPgets32
        .quad _SPgetu32
        .quad _SPmvpasssym
        .quad _SPunbind
        .quad _SPunbind_n
        .quad _SPunbind_to
        .quad _SPprogvrestore
        .quad _SPbind_interrupt_level_0
        .quad _SPbind_interrupt_level_m1
        .quad _SPbind_interrupt_level
        .quad _SPunbind_interrupt_level
        .quad _SParef2
        .quad _SParef3
        .quad _SPaset2
        .quad _SPaset3
        .quad _SPkeyword_bind
        .quad _SPudiv32
        .quad _SPsdiv32
        .quad _SPeabi_ff_call
        .quad _SPdebind
        .quad _SPeabi_callback
        .quad _SPeabi_ff_callhf
local_label(end):       
        	_endfile
