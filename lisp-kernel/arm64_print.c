/*
 * Copyright 2016-2025 Clozure Associates
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

#include <stdio.h>
#include <stdarg.h>
#include <setjmp.h>
#include <string.h>

#include "lisp.h"
#include "area.h"
#include "lisp-exceptions.h"
#include "lisp_globals.h"

void
sprint_lisp_object(LispObj, int);

#define PBUFLEN 252

char printbuf[PBUFLEN + 4];
int bufpos = 0;

jmp_buf escape;

void
add_char(char c)
{
  if (bufpos >= PBUFLEN) {
    longjmp(escape, 1);
  } else {
    printbuf[bufpos++] = c;
  }
}

void
add_string(char *s, int len)
{
  while(len--) {
    add_char(*s++);
  }
}

void
add_lisp_base_string(LispObj str)
{
  lisp_char_code *src = (lisp_char_code *)(ptr_from_lispobj(str + misc_data_offset));
  natural i, n = header_element_count(header_of(str));

  for (i=0; i < n; i++) {
    add_char((char)(*src++));
  }
}

void
add_c_string(char *s)
{
  add_string(s, strlen(s));
}

char numbuf[64];

void
sprint_signed_decimal(signed_natural n)
{
  sprintf(numbuf, "%lld", (long long)n);
  add_c_string(numbuf);
}

void
sprint_unsigned_decimal(natural n)
{
  sprintf(numbuf, "%llu", (unsigned long long)n);
  add_c_string(numbuf);
}

void
sprint_unsigned_hex(natural n)
{
  sprintf(numbuf, "#x%016llx", (unsigned long long)n);
  add_c_string(numbuf);
}

void
sprint_list(LispObj o, int depth)
{
  LispObj the_cdr;

  add_char('(');
  while(1) {
    if (o != lisp_nil) {
      sprint_lisp_object(ptr_to_lispobj(car(o)), depth);
      the_cdr = ptr_to_lispobj(cdr(o));
      if (the_cdr != lisp_nil) {
        add_char(' ');
        if (fulltag_of(the_cdr) == fulltag_cons) {
          o = the_cdr;
          continue;
        }
        add_c_string(". ");
        sprint_lisp_object(the_cdr, depth);
        break;
      }
    }
    break;
  }
  add_char(')');
}

/*
  Print a list of method specializers, using the class name instead
  of the class object.
*/

/* On ARM64, uvector refs span tags 0x40-0x7F (both ivector and gvector refs).
   This replaces the fulltag_misc == check used on other architectures. */
static int
is_heap_ref(unsigned tag)
{
  return (tag >= 0x40 && tag <= 0x7F);
}

void
sprint_specializers_list(LispObj o, int depth)
{
  LispObj the_cdr, the_car;

  add_char('(');
  while(1) {
    if (o != lisp_nil) {
      the_car = car(o);
      if (is_heap_ref(fulltag_of(the_car))) {
        LispObj header = header_of(the_car);
        unsigned subtag = header_subtag(header);

        if (subtag == subtag_instance) {
          if (unbox_fixnum(deref(the_car,1)) < (1<<20)) {
            sprint_lisp_object(deref(deref(the_car,3), 4), depth);
          } else {
            /* An EQL specializer */
            add_c_string("(EQL ");
            sprint_lisp_object(deref(deref(the_car,3), 3), depth);
            add_char(')');
          }
        } else {
          sprint_lisp_object(the_car, depth);
        }
      } else {
        sprint_lisp_object(the_car, depth);
      }
      the_cdr = cdr(o);
      if (the_cdr != lisp_nil) {
        add_char(' ');
        if (fulltag_of(the_cdr) == fulltag_cons) {
          o = the_cdr;
          continue;
        }
        add_c_string(". ");
        sprint_lisp_object(the_cdr, depth);
        break;
      }
    }
    break;
  }
  add_char(')');
}

char *
vector_subtag_name(unsigned subtag)
{
  switch (subtag) {
  case subtag_bit_vector:
    return "BIT-VECTOR";
  case subtag_instance:
    return "INSTANCE";
  case subtag_bignum:
    return "BIGNUM";
  case subtag_u8_vector:
    return "(UNSIGNED-BYTE 8)";
  case subtag_s8_vector:
    return "(SIGNED-BYTE 8)";
  case subtag_u16_vector:
    return "(UNSIGNED-BYTE 16)";
  case subtag_s16_vector:
    return "(SIGNED-BYTE 16)";
  case subtag_u32_vector:
    return "(UNSIGNED-BYTE 32)";
  case subtag_s32_vector:
    return "(SIGNED-BYTE 32)";
  case subtag_u64_vector:
    return "(UNSIGNED-BYTE 64)";
  case subtag_s64_vector:
    return "(SIGNED-BYTE 64)";
  case subtag_package:
    return "PACKAGE";
  case subtag_code_vector:
    return "CODE-VECTOR";
  case subtag_slot_vector:
    return "SLOT-VECTOR";
  default:
    return "";
  }
}


void
sprint_random_vector(LispObj o, unsigned subtag, natural elements)
{
  add_c_string("#<");
  sprint_unsigned_decimal(elements);
  add_c_string("-element vector subtag = ");
  sprintf(numbuf, "%02X @", subtag);
  add_c_string(numbuf);
  sprint_unsigned_hex(o);
  add_c_string(" (");
  add_c_string(vector_subtag_name(subtag));
  add_c_string(")>");
}

void
sprint_symbol(LispObj o)
{
  /* On ARM64, untag(o) = base + node_size; subtract node_size to get struct base */
  lispsymbol *rawsym = (lispsymbol *) ptr_from_lispobj(untag(o) - node_size);
  LispObj
    pname = rawsym->pname,
    package = rawsym->package_predicate;

  if (o == lisp_nil) {
    add_c_string("()");
    return;
  }

  if (fulltag_of(package) == fulltag_cons) {
    package = car(package);
  }

  if (package == nrs_KEYWORD_PACKAGE.vcell) {
    add_char(':');
  }
  add_lisp_base_string(pname);
}

void
sprint_function(LispObj o, int depth)
{
  LispObj lfbits, header, name = lisp_nil;
  natural elements;

  header = header_of(o);
  elements = header_element_count(header);
  lfbits = deref(o, elements);

  if ((lfbits & lfbits_noname_mask) == 0) {
    name = deref(o, elements-1);
  }

  add_c_string("#<");
  if (name == lisp_nil) {
    add_c_string("Anonymous Function ");
  } else {
    if (lfbits & lfbits_method_mask) {
      if (header_subtag(header_of(name)) == subtag_instance) {
        LispObj
          slot_vector = deref(name,3),
          method_name = deref(slot_vector, 6),
          method_qualifiers = deref(slot_vector, 2),
          method_specializers = deref(slot_vector, 3);
        add_c_string("Method-Function ");
        sprint_lisp_object(method_name, depth);
        add_char(' ');
        if (method_qualifiers != lisp_nil) {
          if (cdr(method_qualifiers) == lisp_nil) {
            sprint_lisp_object(car(method_qualifiers), depth);
          } else {
            sprint_lisp_object(method_qualifiers, depth);
          }
          add_char(' ');
        }
        sprint_specializers_list(method_specializers, depth);
      } else {
        sprint_lisp_object(name, depth);
      }
      add_char(' ');
    } else if (lfbits & lfbits_gfn_mask) {
      add_c_string("Generic Function ");
      sprint_lisp_object(name, depth);
      add_char(' ');
    } else {
      add_c_string("Function ");
      sprint_lisp_object(name, depth);
      add_char(' ');
    }
  }
  sprint_unsigned_hex(o);
  add_char('>');
}

void
sprint_gvector(LispObj o, int depth)
{
  LispObj header = header_of(o);
  unsigned
    elements = header_element_count(header),
    subtag = header_subtag(header);

  switch(subtag) {
  case subtag_function:
    sprint_function(o, depth);
    break;

  case subtag_symbol:
    sprint_symbol(o);
    break;

  case subtag_struct:
  case subtag_istruct:
    add_c_string("#<");
    sprint_lisp_object(deref(o,1), depth);
    add_c_string(" @");
    sprint_unsigned_hex(o);
    add_c_string(">");
    break;

  case subtag_simple_vector:
    {
      int i;
      add_c_string("#(");
      for(i = 1; i <= elements; i++) {
        if (i > 1) {
          add_char(' ');
        }
        sprint_lisp_object(deref(o, i), depth);
      }
      add_char(')');
      break;
    }

  case subtag_instance:
    {
      LispObj class_or_hash = deref(o,1);

      if (fulltag_of(class_or_hash) == tag_positive_fixnum ||
          fulltag_of(class_or_hash) == tag_negative_fixnum) {
        sprint_random_vector(o, subtag, elements);
      } else {
        add_c_string("#<CLASS ");
        sprint_lisp_object(class_or_hash, depth);
        add_c_string(" @");
        sprint_unsigned_hex(o);
        add_c_string(">");
      }
      break;
    }

  default:
    sprint_random_vector(o, subtag, elements);
    break;
  }
}

void
sprint_ivector(LispObj o)
{
  LispObj header = header_of(o);
  unsigned
    elements = header_element_count(header),
    subtag = header_subtag(header);

  switch(subtag) {
  case subtag_simple_base_string:
    add_char('"');
    add_lisp_base_string(o);
    add_char('"');
    return;

  case subtag_bignum:
    if (elements == 1) {
      sprint_signed_decimal((signed_natural)(deref(o, 1)));
      return;
    }
    if ((elements == 2) && (deref(o, 2) == 0)) {
      sprint_unsigned_decimal(deref(o, 1));
      return;
    }
    break;

  case subtag_double_float:
    break;

  case subtag_macptr:
    add_c_string("#<MACPTR ");
    sprint_unsigned_hex(deref(o,1));
    add_c_string(">");
    break;

  default:
    sprint_random_vector(o, subtag, elements);
  }
}

void
sprint_vector(LispObj o, int depth)
{
  LispObj header = header_of(o);

  if (immheader_tag_p(fulltag_of(header))) {
    sprint_ivector(o);
  } else {
    sprint_gvector(o, depth);
  }
}

/*
 * ARM64 TBI tag dispatch.
 *
 * Tag byte ranges:
 *   0x00       positive fixnum
 *   0x01       overflowed positive fixnum
 *   0x02       NIL
 *   0x03       cons
 *   0x10-0x1F  immediates (character, single-float, markers)
 *   0x40-0x5F  ivector references
 *   0x60-0x7F  gvector references
 *   0x80-0x9F  ivector headers
 *   0xA0-0xBF  gvector headers
 *   0xFE       overflowed negative fixnum
 *   0xFF       negative fixnum
 */
void
sprint_lisp_object(LispObj o, int depth)
{
  unsigned tag;

  if (--depth < 0) {
    add_char('#');
    return;
  }

  tag = fulltag_of(o);

  /* Fixnums: tag 0x00, 0xFF (and overflow variants 0x01, 0xFE) */
  if (tag == tag_positive_fixnum || tag == tag_negative_fixnum ||
      tag == tag_overflowed_positive_fixnum ||
      tag == tag_overflowed_negative_fixnum) {
    sprint_signed_decimal(unbox_fixnum(o));
    return;
  }

  /* NIL and cons */
  if (tag == tag_nil || tag == tag_cons) {
    sprint_list(o, depth);
    return;
  }

  /* Uvector references (0x40-0x7F): heap-allocated objects */
  if (tag >= 0x40 && tag <= 0x7F) {
    sprint_vector(o, depth);
    return;
  }

  /* Headers (0x80-0xBF): shouldn't appear as bare objects */
  if (tag >= 0x80 && tag <= 0xBF) {
    add_c_string("#<header ? ");
    sprint_unsigned_hex(o);
    add_c_string(">");
    return;
  }

  /* Immediates (0x10-0x1F) */
  if (tag >= 0x10 && tag <= 0x1F) {
    if (o == unbound) {
      add_c_string("#<Unbound>");
    } else if (tag == tag_character) {
      unsigned c = (o >> charcode_shift) & 0xFF;
      add_c_string("#\\");
      if ((c >= ' ') && (c < 0x7f)) {
        add_char(c);
      } else {
        sprintf(numbuf, "%#o", c);
        add_c_string(numbuf);
      }
    } else if (tag == tag_single_float) {
      /* Single-float value is in bits 0-31 */
      LispObj xx = o;
      float f = ((float *)&xx)[0];
      sprintf(numbuf, "%f", (double)f);
      add_c_string(numbuf);
    } else {
      add_c_string("#<imm ");
      sprint_unsigned_hex(o);
      add_c_string(">");
    }
    return;
  }

  /* Fallback: unknown tag */
  sprint_unsigned_hex(o);
}

char *
print_lisp_object(LispObj o)
{
  bufpos = 0;
  if (setjmp(escape) == 0) {
    sprint_lisp_object(o, 5);
    printbuf[bufpos] = 0;
  } else {
    printbuf[PBUFLEN+0] = '.';
    printbuf[PBUFLEN+1] = '.';
    printbuf[PBUFLEN+2] = '.';
    printbuf[PBUFLEN+3] = 0;
  }
  return printbuf;
}

/*
 * Print a GPR value with register label as a Lisp object.
 * Used by the debugger to display register contents.
 */
void
sprint_gpr(ExceptionInformation *xp, char *label, int r)
{
  LispObj val = xpGPR(xp, r);
  fprintf(dbgout, "x%02d/%-10s = %s\n", r, label, print_lisp_object(val));
}

/*
 * Dump all Lisp-relevant registers from a signal context.
 * Lisp-tagged registers (x6-x23) are printed as Lisp objects;
 * control registers are printed as raw hex.
 */
void
print_lisp_context(ExceptionInformation *xp)
{
  sprint_gpr(xp, "rnil",   rnil);
  sprint_gpr(xp, "rt",     rt);
  sprint_gpr(xp, "temp3",  temp3);
  sprint_gpr(xp, "temp2",  temp2);
  sprint_gpr(xp, "temp1",  temp1);
  sprint_gpr(xp, "temp0",  temp0);
  sprint_gpr(xp, "arg_x",  arg_x);
  sprint_gpr(xp, "arg_y",  arg_y);
  sprint_gpr(xp, "arg_z",  arg_z);
  sprint_gpr(xp, "save0",  save0);
  sprint_gpr(xp, "save1",  save1);
  sprint_gpr(xp, "save2",  save2);
  sprint_gpr(xp, "save3",  save3);
  sprint_gpr(xp, "save4",  save4);
  sprint_gpr(xp, "save5",  save5);
  sprint_gpr(xp, "save6",  save6);
  sprint_gpr(xp, "save7",  save7);
  fprintf(dbgout, "x%02d/%-10s = 0x%016llx\n", vsp, "vsp",
          (unsigned long long)xpGPR(xp, vsp));
  fprintf(dbgout, "x%02d/%-10s = 0x%016llx\n", allocptr, "allocptr",
          (unsigned long long)xpGPR(xp, allocptr));
  fprintf(dbgout, "x%02d/%-10s = 0x%016llx\n", allocbase, "allocbase",
          (unsigned long long)xpGPR(xp, allocbase));
  fprintf(dbgout, "x%02d/%-10s = 0x%016llx\n", rcontext, "rcontext",
          (unsigned long long)xpGPR(xp, rcontext));
  fprintf(dbgout, "PC             = 0x%016llx\n", (unsigned long long)xpPC(xp));
  fprintf(dbgout, "LR             = 0x%016llx\n", (unsigned long long)xpLR(xp));
  fprintf(dbgout, "SP             = 0x%016llx\n", (unsigned long long)xpSP(xp));
}
