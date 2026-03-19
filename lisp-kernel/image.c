/*
 * Copyright 2002-2009 Clozure Associates
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

#include "lisp.h"
#include "lisp_globals.h"
#include "area.h"
#include "image.h"
#include "gc.h"
#include <errno.h>
#include <unistd.h>
#ifndef WINDOWS
#include <sys/mman.h>
#endif
#include <stdio.h>
#include <limits.h>
#include <time.h>


#ifdef ARM64
/* ARM64 TBI tags: can't use bitmask (uvector_ref=0x40, 1<<64 overflows).
   Relocatable tags: nil, cons, and uvector references (bit 6 set, bit 7 clear). */
#define is_relocatable_tag(t) \
  ((t) == tag_nil || (t) == tag_cons || (((t) & uvector_mask) == uvector_ref))
/* Strip TBI tag (top byte) for range checks — address is in low 56 bits */
#define addr_of(w) ((w) & 0x00FFFFFFFFFFFFFFULL)
#else
#if defined(PPC64) || defined(X8632)
#define RELOCATABLE_FULLTAG_MASK \
  ((1<<fulltag_cons)|(1<<fulltag_misc))
#elif defined(X8664)
#define RELOCATABLE_FULLTAG_MASK \
  ((1<<fulltag_cons)|(1<<fulltag_misc)|(1<<fulltag_symbol)|(1<<fulltag_function))
#else
#define RELOCATABLE_FULLTAG_MASK \
  ((1<<fulltag_cons)|(1<<fulltag_nil)|(1<<fulltag_misc))
#endif
#define is_relocatable_tag(t) ((1<<(t)) & RELOCATABLE_FULLTAG_MASK)
#define addr_of(w) (w)
#endif

void
relocate_area_contents(area *a, LispObj bias)
{
  LispObj 
    *start = (LispObj *)(a->low), 
    *end = (LispObj *)(a->active),
    low = (LispObj)image_base - bias,
    high = ptr_to_lispobj(active_dynamic_area->active) - bias,
    w0, w1;
  int fulltag;
  Boolean fixnum_after_header_is_link = false;

  while (start < end) {
    w0 = *start;
    fulltag = fulltag_of(w0);
    if (immheader_tag_p(fulltag)) {
      start = (LispObj *)skip_over_ivector((natural)start, w0);
    } else {
#ifdef X86
      if (header_subtag(w0) == subtag_function) {
#ifdef X8664
        int skip = ((int) start[1])+1;
#else
        extern void update_self_references(LispObj *);
        extern natural imm_word_count(LispObj);

        natural skip = (natural)imm_word_count(((LispObj)start)+fulltag_misc)+1;
        update_self_references(start);
#endif
     
        start += skip;
        if (((LispObj) start) & node_size) {
          --start;
        }
        w0 = *start;
        fulltag = fulltag_of(w0);
      }
#endif
#ifdef ARM
      if ((header_subtag(w0) == subtag_function) ||
          (header_subtag(w0) == subtag_pseudofunction)) {
        w1 = start[1];
        if ((w1 >= low) && (w1 < high)) {
          start[1]=(w1+bias);
        }
        start+=2;
        w0 = *start;
        fulltag = fulltag_of(w0);
      }
#endif
#ifdef ARM64
      /* On ARM64, function.entrypoint (slot 0 = start[1]) is an untagged
         code address that won't be relocated by the normal tag-based
         relocator.  Relocate it explicitly, like ARM32. */
      if (header_subtag(w0) == subtag_function) {
        w1 = start[1];
        if ((w1 >= low) && (w1 < high)) {
          start[1]=(w1+bias);
          static int ep_reloc_count = 0;
          if (ep_reloc_count < 3) {
            fprintf(dbgout, "  ep-reloc[%d]: fn=%p old=0x%lx new=0x%lx cv=0x%lx\n",
                    ep_reloc_count, (void*)start, (unsigned long)w1,
                    (unsigned long)start[1], (unsigned long)start[2]);
          }
          ep_reloc_count++;
        } else {
          static int ep_skip_count = 0;
          if (ep_skip_count < 3) {
            fprintf(dbgout, "  ep-SKIP[%d]: fn=%p ep=0x%lx low=0x%lx high=0x%lx cv=0x%lx\n",
                    ep_skip_count, (void*)start, (unsigned long)w1,
                    (unsigned long)low, (unsigned long)high, (unsigned long)start[2]);
          }
          ep_skip_count++;
        }
        start+=2;
        w0 = *start;
        fulltag = fulltag_of(w0);
      }
#endif
      if (header_subtag(w0) == subtag_weak) {
        fixnum_after_header_is_link = true;
      }
      if (header_subtag(w0) == subtag_hash_vector) {
        hash_table_vector_header *hashp = (hash_table_vector_header *)start;
        
        if (hashp->flags & nhash_track_keys_mask) {
          hashp->flags |= nhash_key_moved_mask;
        }
        fixnum_after_header_is_link = true;
      }

      if ((addr_of(w0) >= low) && (addr_of(w0) < high) &&
	  is_relocatable_tag(fulltag)) {
	*start = (w0+bias);
      }
      w1 = *++start;
      fulltag = fulltag_of(w1);
      if ((addr_of(w1) >= low) && (addr_of(w1) < high) &&
	  (fixnum_after_header_is_link ||
           is_relocatable_tag(fulltag))) {
	*start = (w1+bias);
      }
      fixnum_after_header_is_link = false;
      ++start;
    }
  }
  if (start > end) {
    Bug(NULL, "Overran area bounds in relocate_area_contents");
  }
}
      



off_t
seek_to_next_page(int fd)
{
  off_t pos = LSEEK(fd, 0, SEEK_CUR);
  pos = align_to_power_of_2(pos, log2_page_size);
  return LSEEK(fd, pos, SEEK_SET);
}
  
/*
  fd is positioned to EOF; header has been allocated by caller.
  If we find a trailer (and that leads us to the header), read
  the header & return true else return false.
*/
Boolean
find_openmcl_image_file_header(int fd, openmcl_image_file_header *header)
{
  openmcl_image_file_trailer trailer;
  int disp;
  off_t pos;
  unsigned version, flags;

  pos = LSEEK(fd, 0, SEEK_END);
  if (pos < 0) {
    return false;
  }
  pos -= sizeof(trailer);

  if (LSEEK(fd, pos, SEEK_SET) < 0) {
    return false;
  }
  if (read(fd, &trailer, sizeof(trailer)) != sizeof(trailer)) {
    return false;
  }
  if ((trailer.sig0 != IMAGE_SIG0) ||
      (trailer.sig1 != IMAGE_SIG1) ||
      (trailer.sig2 != IMAGE_SIG2)) {
    return false;
  }
  disp = trailer.delta;
  
  if (disp >= 0) {
    return false;
  }
  if (LSEEK(fd, disp, SEEK_CUR) < 0) {
    return false;
  }
  if (read(fd, header, sizeof(openmcl_image_file_header)) !=
      sizeof(openmcl_image_file_header)) {
    return false;
  }
  if ((header->sig0 != IMAGE_SIG0) ||
      (header->sig1 != IMAGE_SIG1) ||
      (header->sig2 != IMAGE_SIG2) ||
      (header->sig3 != IMAGE_SIG3)) {
    return false;
  }
  version = (header->abi_version) & 0xffff;
  if (version < ABI_VERSION_MIN) {
    fprintf(dbgout, "Heap image (version %d) "
	    "is too old for this kernel (minimum %d).\n", version,
	    ABI_VERSION_MIN);
    return false;
  }
  if (version > ABI_VERSION_MAX) {
    fprintf(dbgout, "Heap image (version %d) "
	    "is too new for this kernel (maximum %d).\n", version,
	    ABI_VERSION_MAX);
    return false;
  }
  flags = header->flags;
  fprintf(dbgout, "Image flags=%u, PLATFORM=%u, nsections=%u, abi_version=%u\n",
          flags, PLATFORM, header->nsections, header->abi_version & 0xffff);
  if (flags != PLATFORM) {
    fprintf(dbgout, "Heap image was saved for another platform.\n");
    return false;
  }
  return true;
}

void
load_image_section(int fd, openmcl_image_section_header *sect)
{
  extern area* allocate_dynamic_area(natural);
  off_t
    pos = seek_to_next_page(fd), advance;
  natural
    mem_size = sect->memory_size;
  char *addr;
  area *a;

  advance = mem_size;
  fprintf(dbgout, "load_image_section: code=%ld, mem_size=%ld (0x%lx), pos=%lld\n",
          (long)sect->code, (long)mem_size, (long)mem_size, (long long)pos);
  switch(sect->code) {
  case AREA_READONLY:
    fprintf(dbgout, "  READONLY: mapping at %p, size=%ld\n", pure_space_active, (long)mem_size);
    if (mem_size != 0) {
      if (!MapFile(pure_space_active,
                   pos,
                   align_to_power_of_2(mem_size,log2_page_size),
#ifdef ARM64
                   MEMPROTECT_RW,  /* map as RW first, mprotect to RX after */
#else
                   MEMPROTECT_RX,
#endif
                   fd)) {
        return;
      }
    }
    a = new_area(pure_space_active, pure_space_limit, AREA_READONLY);
    pure_space_active += mem_size;
    a->active = pure_space_active;
    sect->area = a;      
    break;

  case AREA_STATIC:
    fprintf(dbgout, "  STATIC: mapping at %p, size=%ld\n", static_space_active, (long)mem_size);
    if (!MapFile(static_space_active,
		 pos,
		 align_to_power_of_2(mem_size,log2_page_size),
		 MEMPROTECT_RWX,
		 fd)) {
      return;
    }
    a = new_area(static_space_active, static_space_limit, AREA_STATIC);
    static_space_active += mem_size;
    a->active = static_space_active;
    sect->area = a;
    break;

  case AREA_DYNAMIC:
    a = allocate_dynamic_area(mem_size);
    fprintf(dbgout, "  DYNAMIC: mapping at %p, size=%ld\n", a ? a->low : NULL, (long)mem_size);
    if (!MapFile(a->low,
		 pos,
		 align_to_power_of_2(mem_size,log2_page_size),
		 MEMPROTECT_RWX,
		 fd)) {
      return;
    }

    a->static_dnodes = sect->static_dnodes;
    sect->area = a;
    break;

  case AREA_MANAGED_STATIC:
    fprintf(dbgout, "  MANAGED_STATIC: size=%ld\n", (long)mem_size);
    a = new_area(pure_space_limit, pure_space_limit+align_to_power_of_2(mem_size,log2_page_size), AREA_MANAGED_STATIC);
    a->active = a->low+mem_size;
    if (mem_size) {
      natural
        refbits_size = align_to_power_of_2((((mem_size>>dnode_shift)+7)>>3),
                                           log2_page_size);
      if (!MapFile(a->low,
                   pos,
                   align_to_power_of_2(mem_size,log2_page_size),
                   MEMPROTECT_RWX,
                   fd)) {
        return;
      }
      if (!CommitMemory(global_mark_ref_bits,refbits_size)) {
        return;
      }
      /* Need to save/restore persistent refbits. */
      if (!MapFile(managed_static_refbits,
                   align_to_power_of_2(pos+mem_size,log2_page_size),
                   refbits_size,
                   MEMPROTECT_RW,
                   fd)) {
        return;
      }
      /* Should change image format and store this in the image */
      {
        natural ndnodes = area_dnode(a->active, a->low), i;
        if (!CommitMemory(managed_static_refidx,(((ndnodes +255)>>8)+7)>>3)) {
          return;
        }
        for (i=0; i < ndnodes; i++) {
          if (ref_bit(managed_static_refbits,i)) {
            set_bit(managed_static_refidx,i>>8);
          }
        }
      }
      advance += refbits_size;
    }
    sect->area = a;
    a->ndnodes = area_dnode(a->active, a->low);
    managed_static_area = a;
    lisp_global(REF_BASE) = (LispObj) a->low;
    break;

    /* In many respects, the static_cons_area is part of the dynamic
       area; it's physically adjacent to it (immediately precedes the
       dynamic area in memory) and its contents are subject to full
       GC (but not compaction.)  It's maintained as a seperate section
       in the image file, at least for now. */


  case AREA_STATIC_CONS:
    fprintf(dbgout, "  STATIC_CONS: size=%ld\n", (long)mem_size);
    addr = (char *) lisp_global(HEAP_START);
    tenured_area = new_area(addr, addr, AREA_STATIC);

    a = new_area(addr-align_to_power_of_2(mem_size,log2_page_size), addr, AREA_STATIC_CONS);
    if (mem_size) {
      if (!MapFile(a->low,
                   pos,
                   align_to_power_of_2(mem_size,log2_page_size),
                   MEMPROTECT_RWX,
                   fd)) {
        return;
      }
    }
    a->ndnodes = area_dnode(a->active, a->low);
    sect->area = a;
    static_cons_area = a;
    /* not yet 
    lower_heap_start(a->low,tenured_area);
    */
    break;

  default:
    return;
    
  }
  LSEEK(fd, pos+advance, SEEK_SET);
}

LispObj
load_openmcl_image(int fd, openmcl_image_file_header *h)
{
  LispObj image_nil = 0;
  area *a;
  fprintf(dbgout, "load_openmcl_image: image_base=0x%lx\n", (unsigned long)image_base);
  if (find_openmcl_image_file_header(fd, h)) {
    int i, nsections = h->nsections;
    openmcl_image_section_header sections[nsections], *sect=sections;
    LispObj bias = image_base - ACTUAL_IMAGE_BASE(h);
    fprintf(dbgout, "  ACTUAL_IMAGE_BASE=0x%lx, bias=0x%lx\n",
            (unsigned long)ACTUAL_IMAGE_BASE(h), (unsigned long)bias);
#if (WORD_SIZE== 64)
    signed_natural section_data_delta = 
      ((signed_natural)(h->section_data_offset_high) << 32L) | h->section_data_offset_low;
#endif

    if (read (fd, sections, nsections*sizeof(openmcl_image_section_header)) !=
	nsections * sizeof(openmcl_image_section_header)) {
      return 0;
    }
#if WORD_SIZE == 64
    LSEEK(fd, section_data_delta, SEEK_CUR);
#endif
    for (i = 0; i < nsections; i++, sect++) {
      load_image_section(fd, sect);
      a = sect->area;
      if (a == NULL) {
	return 0;
      }
    }

    for (i = 0, sect = sections; i < nsections; i++, sect++) {
      a = sect->area;
      switch(sect->code) {
      case AREA_STATIC:
	nilreg_area = a;
#ifdef PPC
#ifdef PPC64
        image_nil = ptr_to_lispobj(a->low + (1024*4) + sizeof(lispsymbol) + fulltag_misc);
#else
	image_nil = (LispObj)(a->low + 8 + 8 + (1024*4) + fulltag_nil);
#endif
#endif
#ifdef X86
#ifdef X8664
	image_nil = (LispObj)(a->low) + (1024*4) + fulltag_nil;
#else
	image_nil = (LispObj)(a->low) + (1024*4) + fulltag_cons;
#endif
#endif
#ifdef ARM
	image_nil = (LispObj)(a->low) + (1024*4) + fulltag_nil;
#endif
#ifdef ARM64
	image_nil = nil_value;
#endif
	fprintf(dbgout, "  image_nil = 0x%lx\n", (unsigned long)image_nil);
	set_nil(image_nil);
	fprintf(dbgout, "  set_nil done, bias=0x%lx\n", (unsigned long)bias);
	if (bias) {
          LispObj weakvll = lisp_global(WEAKVLL);

          if ((addr_of(weakvll) >= ((LispObj)image_base-bias)) &&
              (addr_of(weakvll) < (ptr_to_lispobj(active_dynamic_area->active)-bias))) {
            lisp_global(WEAKVLL) = weakvll+bias;
          }
	  fprintf(dbgout, "  relocating static area...\n");
	  relocate_area_contents(a, bias);
	  fprintf(dbgout, "  static relocation done\n");
	}
	make_dynamic_heap_executable(a->low, a->active);
	fprintf(dbgout, "  AREA_STATIC processing done\n");
        add_area_holding_area_lock(a);
	fprintf(dbgout, "  AREA_STATIC added\n");
        break;

      case AREA_READONLY:
        if (bias && 
            (managed_static_area->active != managed_static_area->low)) {
          UnProtectMemory(a->low, a->active-a->low);
          relocate_area_contents(a, bias);
          ProtectMemory(a->low, a->active-a->low);
        }
        readonly_area = a;
	add_area_holding_area_lock(a);
	fprintf(dbgout, "  AREA_READONLY done\n");
	break;
      }
    }
    fprintf(dbgout, "  Starting pass 3 (managed_static, static_cons, dynamic)\n");
    for (i = 0, sect = sections; i < nsections; i++, sect++) {
      a = sect->area;
      switch(sect->code) {
      case AREA_MANAGED_STATIC:
        if (bias) {
          relocate_area_contents(a, bias);
        }
        add_area_holding_area_lock(a);
        break;
      case AREA_STATIC_CONS:
	if (bias) {
	  LispObj static_conses = lisp_global(STATIC_CONSES);
	  if (static_conses && static_conses != lisp_nil) {
	    lisp_global(STATIC_CONSES) += bias;
	    relocate_area_contents(a, bias);
	  }
	}
        /* not yet
 lower_heap_start(static_cons_area->low,tenured_area);
        */
        break;
      case AREA_DYNAMIC:
        fprintf(dbgout, "  relocating dynamic area...\n");
        if (bias) {
          relocate_area_contents(a, bias);
        }
        fprintf(dbgout, "  dynamic relocation done, resizing heap\n");
        fprintf(dbgout, "  BEFORE resize: a->low=0x%lx a->active=0x%lx a->high=0x%lx threshold=0x%lx\n",
                (unsigned long)a->low, (unsigned long)a->active, (unsigned long)a->high,
                (unsigned long)lisp_heap_gc_threshold);
	resize_dynamic_heap(a->active, lisp_heap_gc_threshold);
        fprintf(dbgout, "  AFTER resize: a->low=0x%lx a->active=0x%lx a->high=0x%lx\n",
                (unsigned long)a->low, (unsigned long)a->active, (unsigned long)a->high);
	xMakeDataExecutable(a->low, a->active - a->low);
        fprintf(dbgout, "  AREA_DYNAMIC done\n");
	break;
      }
    }
  }
  /* Bug 124: TLB binding-index scaling REMOVED.
     On ARM64 with fixnumshift=0, l0-symbol.lisp increments binding-index by 8
     (= node_size), so indices are already byte offsets. No image-load scaling needed. */
  fprintf(dbgout, "  load_openmcl_image returning image_nil=0x%lx\n", (unsigned long)image_nil);
  /* Bug 165 diagnostic: scan dynamic area for istructs with 16 elements,
     dump their slot 12 (nhash.find) to check hash table validity */
  {
    area *da = active_dynamic_area;
    if (da) {
      LispObj *scan = (LispObj *)da->low;
      LispObj *end = (LispObj *)da->active;
      int ht_count = 0;
      fprintf(dbgout, "  Bug165: scanning dynamic area for hash tables...\n");
      while (scan < end) {
        LispObj header = *scan;
        natural subtag = header >> 56;
        natural count = header & 0x00FFFFFFFFFFFFFFULL;
        if (subtag == 0xae && count == 16) {
          /* istruct with 16 elements = likely hash table */
          LispObj *data = scan + 1; /* data starts after header */
          ht_count++;
          if (ht_count <= 10) {
            fprintf(dbgout, "    HT#%d @%p: slot0=%016lx slot12(find)=%016lx slot15(min-size)=%016lx\n",
                    ht_count, (void*)scan,
                    (unsigned long)data[0], (unsigned long)data[12], (unsigned long)data[15]);
            /* Check if slot12 looks wrong (not a function/symbol) */
            natural s12_tag = data[12] >> 56;
            if (s12_tag != 0x62 && s12_tag != 0x63 && data[12] != 0) {
              fprintf(dbgout, "    *** SUSPICIOUS: slot12 tag=0x%02lx (expected 0x62 function or 0x63 symbol) ***\n",
                      (unsigned long)s12_tag);
              /* Dump all 16 slots */
              for (int si = 0; si < 16; si++) {
                fprintf(dbgout, "      slot[%2d] = %016lx (tag=0x%02lx)\n",
                        si, (unsigned long)data[si], (unsigned long)(data[si] >> 56));
              }
            }
          }
          scan += 1 + count; /* skip header + 16 elements */
        } else {
          /* Skip this object */
          if (subtag >= 0x80) {
            /* uvector: header + data words */
            natural nwords;
            if (subtag >= 0xa0) {
              /* node vector: count = element_count */
              nwords = count;
            } else {
              /* imm vector: need to compute from element count and subtag */
              /* For simplicity, use dnode-aligned size */
              nwords = (count + 1) & ~1; /* rough alignment */
            }
            scan += 1 + nwords;
            /* Align to dnode */
            scan = (LispObj *)(((natural)scan + 15) & ~15);
          } else {
            scan += 2; /* cons or other pair */
          }
        }
      }
      fprintf(dbgout, "  Bug165: found %d hash tables in dynamic area\n", ht_count);
    }
  }
  return image_nil;
}
 
void
prepare_to_write_dynamic_space(area *a)
{
  LispObj 
    *start = (LispObj *)(a->low),
    *end = (LispObj *) (a->active),
    x1;
  int tag, subtag, element_count;

  while (start < end) {
    x1 = *start;
    tag = fulltag_of(x1);
    if (immheader_tag_p(tag)) {
      subtag = header_subtag(x1);
      if (subtag == subtag_macptr) {
        if ((start[1] >= (natural)0x10000) && (start[1] < (natural)-0x10000)) {
          /* Leave small pointers alone */
          *start = make_header(subtag_dead_macptr,header_element_count(x1));
        }
      }
      start = (LispObj *)skip_over_ivector((natural)start, x1);
    } else if (nodeheader_tag_p(tag)) {
      element_count = header_element_count(x1) | 1;
      start += (element_count+1);
    } else {
      start += 2;
    }
  }
}

  

int
write_file_and_section_headers(int fd, 
                               openmcl_image_file_header *file_header,
                               openmcl_image_section_header* section_headers,
                               int nsections,
                               off_t *header_pos)
{
  *header_pos = seek_to_next_page(fd);

  if (LSEEK (fd, *header_pos, SEEK_SET) < 0) {
    return errno;
  }
  if (write(fd, file_header, sizeof(*file_header)) != sizeof(*file_header)) {
    return errno;
  }
  if (write(fd, section_headers, sizeof(section_headers[0])*nsections)
      != (sizeof(section_headers[0])*nsections)) {
    return errno;
  }
  return 0;
}
  
natural
writebuf(int fd, char *bytes, natural n)
{
  natural remain = n, this_size;
  signed_natural result;

  while (remain) {
    this_size = remain;
    if (this_size > INT_MAX) {
      this_size = INT_MAX;
    }
    result = write(fd, bytes, this_size);
    if (result < 0) {
      return errno;
    }
    bytes += result;

    remain -= result;
  }
  return 0;
}

void
prepare_to_write_static_space(Boolean egc_was_enabled)
{
  area *g0_area = g1_area->younger;
  int i;

  /* Save GC config */
  lisp_global(LISP_HEAP_THRESHOLD) = lisp_heap_gc_threshold;
  lisp_global(G0_THRESHOLD) = g0_area->threshold;
  lisp_global(G1_THRESHOLD) = g1_area->threshold;
  lisp_global(G2_THRESHOLD) = g2_area->threshold;
  lisp_global(EGC_ENABLED) = (LispObj)egc_was_enabled;
  lisp_global(GC_NOTIFY_THRESHOLD) = lisp_heap_notify_threshold;
  /*
    lisp_global(GC_NUM) and lisp_global(FWDNUM) are persistent,
    as is DELETED_STATIC_PAIRS.
    Nothing else is even meaningful at this point.
    Except for those things that've become meaningful since that
    comment was written.
  */
  for (i = MIN_KERNEL_GLOBAL; i < 0; i++) {
    switch (i) {
    case FREE_STATIC_CONSES:
    case FWDNUM:
    case GC_NUM:
    case STATIC_CONSES:
    case WEAK_GC_METHOD:
    case LISP_HEAP_THRESHOLD:
    case EGC_ENABLED:
    case G0_THRESHOLD:
    case G1_THRESHOLD:
    case G2_THRESHOLD:
    case GC_NOTIFY_THRESHOLD:
      break;
    case WEAKVLL:
      break;
    default:
      lisp_global(i) = 0;
    }
  }
}


OSErr
save_application_internal(unsigned fd, Boolean egc_was_enabled)
{
  openmcl_image_file_header fh;
  openmcl_image_section_header sections[NUM_IMAGE_SECTIONS];
  openmcl_image_file_trailer trailer;
  area *areas[NUM_IMAGE_SECTIONS], *a;
  int i, err;
  off_t header_pos, eof_pos;
#if WORD_SIZE == 64
  off_t image_data_pos;
  signed_natural section_data_delta;
#endif

  /*
    Coerce macptrs to dead_macptrs.
  */
  
  prepare_to_write_dynamic_space(active_dynamic_area);
  prepare_to_write_dynamic_space(managed_static_area);

  /* 
     If we ever support continuing after saving an image,
     undo this .. */

  if (static_cons_area->high > static_cons_area->low) {
    active_dynamic_area->low = static_cons_area->high;
    tenured_area->static_dnodes -= area_dnode(static_cons_area->high, static_cons_area->low);
  }

  areas[0] = nilreg_area; 
  areas[1] = readonly_area;
  areas[2] = active_dynamic_area;
  areas[3] = managed_static_area;
  areas[4] = static_cons_area;
  for (i = 0; i < NUM_IMAGE_SECTIONS; i++) {
    a = areas[i];
    sections[i].code = a->code;
    sections[i].area = NULL;
    sections[i].memory_size  = a->active - a->low;
    if (a == active_dynamic_area) {
      sections[i].static_dnodes = tenured_area->static_dnodes;
    } else {
      sections[i].static_dnodes = 0;
    }
  }
  fh.sig0 = IMAGE_SIG0;
  fh.sig1 = IMAGE_SIG1;
  fh.sig2 = IMAGE_SIG2;
  fh.sig3 = IMAGE_SIG3;
  fh.timestamp = time(NULL);
  CANONICAL_IMAGE_BASE(&fh) = IMAGE_BASE_ADDRESS;
  ACTUAL_IMAGE_BASE(&fh) = image_base;
  fh.nsections = NUM_IMAGE_SECTIONS;
  fh.abi_version=ABI_VERSION_CURRENT;
#if WORD_SIZE == 64
  fh.section_data_offset_high = 0;
  fh.section_data_offset_low = 0;
#else
  fh.pad0[0] = fh.pad0[1] = 0;
  fh.pad1[0] = fh.pad1[1] = fh.pad1[2] = fh.pad1[3] = 0;
#endif
  fh.flags = PLATFORM;

#if WORD_SIZE == 64
  image_data_pos = seek_to_next_page(fd);
#else
  err = write_file_and_section_headers(fd, &fh, sections, NUM_IMAGE_SECTIONS, &header_pos);
  if (err) {
    return err;
  }
#endif

  prepare_to_write_static_space(egc_was_enabled);



  for (i = 0; i < NUM_IMAGE_SECTIONS; i++) {
    natural n;
    a = areas[i];
    seek_to_next_page(fd);
    n = sections[i].memory_size;
    if (writebuf(fd, a->low, n)) {
	return errno;
    }
    if (n &&  ((sections[i].code) == AREA_MANAGED_STATIC)) {
      natural ndnodes = area_dnode(a->active, a->low);
      natural nrefbytes = align_to_power_of_2((ndnodes+7)>>3,log2_page_size);

      seek_to_next_page(fd);
      if (writebuf(fd,(char*)managed_static_refbits,nrefbytes)) {
        return errno;
      }
    }
  }

#if WORD_SIZE == 64
  seek_to_next_page(fd);
  section_data_delta = -((LSEEK(fd,0,SEEK_CUR)+sizeof(fh)+sizeof(sections)) -
                         image_data_pos);
  fh.section_data_offset_high = (int)(section_data_delta>>32L);
  fh.section_data_offset_low = (unsigned)section_data_delta;
  err =  write_file_and_section_headers(fd, &fh, sections, NUM_IMAGE_SECTIONS, &header_pos);
  if (err) {
    return err;
  }  
#endif

  trailer.sig0 = IMAGE_SIG0;
  trailer.sig1 = IMAGE_SIG1;
  trailer.sig2 = IMAGE_SIG2;
  eof_pos = LSEEK(fd, 0, SEEK_CUR) + sizeof(trailer);
  trailer.delta = (int) (header_pos-eof_pos);
  if (write(fd, &trailer, sizeof(trailer)) == sizeof(trailer)) {
#ifndef WINDOWS
    fsync(fd);
#endif
    close(fd);
    return 0;
  } 
  i = errno;
  close(fd);
  return i;
}

OSErr
save_application(int fd, Boolean egc_was_enabled)
{
#ifdef DARWIN
#ifdef X86
  extern void save_native_library(int, Boolean);
 
  if (fd < 0) {
    save_native_library(-fd, egc_was_enabled);
    return 0;
  }
#endif
#endif
  return save_application_internal(fd, egc_was_enabled);
}

      



