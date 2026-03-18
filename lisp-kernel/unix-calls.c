/*
 * Copyright 2008-2009 Clozure Associates
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

/* Provide wrappers around some standard C library functions that
   can't easily be called from CCL's FFI for some reason (or where
   we want to override/extend the function's default behavior.)
 
   Functions in this file should be referenced via the kernel
   imports table.

   Callers should generally expect standard C library error-handling
   conventions (e.g., return -1 or NULL and set errno on error.)
*/

#ifndef _LARGEFILE64_SOURCE
#define _LARGEFILE64_SOURCE
#endif
#include <errno.h>
#include <unistd.h>
#include <sys/stat.h>
#include <dirent.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <stdint.h>
#include <signal.h>
#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/mman.h>
#ifdef ARM64
#include <mach/mach.h>
#include <mach/thread_act.h>
#endif

/* Debug global: address of FASL buffer cursor (8 bytes before data area) */
#ifdef ARM64
#include <pthread.h>
volatile void *dbg_fasl_cursor_addr = NULL;
volatile unsigned long long dbg_fasl_cursor_expected = 0;
/* Bug 162 diagnostic: set to 1 to make fd-tell return 0, forcing
   %simple-fasl-set-file-pos to always use lseek instead of the
   cursor-incf shortcut. If corruption stops, the bug is in the
   %%get-signed-longlong incf path. If corruption persists, it's
   in %simple-fasl-read-byte's cursor update. */
int dbg_force_fasl_lseek = 0;  /* Bug 162: set to 1 to bypass cursor-incf */

/* Bug 162: polling thread that detects cursor corruption and
   suspends the main thread to examine its state. */
static pthread_t dbg_main_thread;
static volatile int dbg_monitor_active = 0;

/* Bug 162: Set hardware watchpoint on cursor via Mach debug registers */
static int dbg_set_hw_watchpoint(mach_port_t thread, void *addr) {
    arm_debug_state64_t dbg_state;
    mach_msg_type_number_t count = ARM_DEBUG_STATE64_COUNT;
    kern_return_t kr;

    /* Get current debug state */
    kr = thread_get_state(thread, ARM_DEBUG_STATE64,
                          (thread_state_t)&dbg_state, &count);
    if (kr != KERN_SUCCESS) {
        fprintf(stderr, "DBG: Failed to get debug state: %d\n", kr);
        return -1;
    }

    /* Set watchpoint 0: write-only, 8 bytes, at addr */
    dbg_state.__wvr[0] = (uint64_t)addr;
    /* WCR: enabled, user-mode, write-only, 8-byte match
       Bits: [0]=enable, [2:1]=PAC(user=2), [4:3]=LSC(write=2), [12:5]=BAS(0xFF=8byte) */
    dbg_state.__wcr[0] = (0xFF << 5) | (2 << 3) | (2 << 1) | 1;

    kr = thread_set_state(thread, ARM_DEBUG_STATE64,
                          (thread_state_t)&dbg_state, ARM_DEBUG_STATE64_COUNT);
    if (kr != KERN_SUCCESS) {
        fprintf(stderr, "DBG: Failed to set watchpoint: %d\n", kr);
        return -1;
    }
    fprintf(stderr, "DBG: Hardware watchpoint set at %p\n", addr);
    return 0;
}

static void *dbg_cursor_monitor(void *arg) {
    volatile unsigned long long *cursor_ptr = (volatile unsigned long long *)arg;
    unsigned long long prev = *cursor_ptr;
    unsigned long long checks = 0;

    /* Wait for cursor to advance to buf+4 (4 bytes read), then arm watchpoint.
       From previous runs, corruption happens after 4 bytes are read.
       cursor starts at cursor_addr+8, after 4 reads = cursor_addr+12 = cursor_addr+0xc */
    unsigned long long arm_value = (unsigned long long)cursor_ptr + 0xc;
    int wp_armed = 0;

    while (dbg_monitor_active) {
        unsigned long long cv = *cursor_ptr;
        checks++;

        /* Arm watchpoint when cursor reaches the expected pre-corruption value */
        if (!wp_armed && cv == arm_value) {
            mach_port_t main_mach = pthread_mach_thread_np(dbg_main_thread);
            thread_suspend(main_mach);
            if (dbg_set_hw_watchpoint(main_mach, (void *)cursor_ptr) == 0) {
                wp_armed = 1;
            }
            thread_resume(main_mach);
        }
        if (cv != 0 && cv < 0x10000) {
            /* Corruption detected! Suspend main thread and dump state. */
            fprintf(stderr, "\n!!! Bug 162: CURSOR CORRUPTION DETECTED by monitor thread !!!\n");
            fprintf(stderr, "  cursor_addr = %p\n", (void *)cursor_ptr);
            fprintf(stderr, "  corrupted_value = 0x%llx (prev = 0x%llx)\n", cv, prev);
            fprintf(stderr, "  checks = %llu\n", checks);

            /* Suspend main thread and read its state via Mach API */
            mach_port_t main_mach = pthread_mach_thread_np(dbg_main_thread);
            thread_suspend(main_mach);

            arm_thread_state64_t state;
            mach_msg_type_number_t count = ARM_THREAD_STATE64_COUNT;
            kern_return_t kr = thread_get_state(main_mach,
                                                ARM_THREAD_STATE64,
                                                (thread_state_t)&state,
                                                &count);
            if (kr == KERN_SUCCESS) {
                fprintf(stderr, "  Main thread state at time of corruption:\n");
                fprintf(stderr, "    PC  = 0x%llx\n", (unsigned long long)state.__pc);
                fprintf(stderr, "    LR  = 0x%llx\n", (unsigned long long)state.__lr);
                fprintf(stderr, "    SP  = 0x%llx\n", (unsigned long long)state.__sp);
                fprintf(stderr, "    FP  = 0x%llx\n", (unsigned long long)state.__fp);
                fprintf(stderr, "    x0  = 0x%llx  x1  = 0x%llx\n",
                        (unsigned long long)state.__x[0], (unsigned long long)state.__x[1]);
                fprintf(stderr, "    x2  = 0x%llx  x3  = 0x%llx\n",
                        (unsigned long long)state.__x[2], (unsigned long long)state.__x[3]);
                fprintf(stderr, "    x9  = 0x%llx  x10 = 0x%llx\n",
                        (unsigned long long)state.__x[9], (unsigned long long)state.__x[10]);
                fprintf(stderr, "    x11 = 0x%llx  x12 = 0x%llx\n",
                        (unsigned long long)state.__x[11], (unsigned long long)state.__x[12]);
                fprintf(stderr, "    x13 = 0x%llx  x14 = 0x%llx\n",
                        (unsigned long long)state.__x[13], (unsigned long long)state.__x[14]);
                fprintf(stderr, "    x15 = 0x%llx  x16 = 0x%llx\n",
                        (unsigned long long)state.__x[15], (unsigned long long)state.__x[16]);
                fprintf(stderr, "    x25(vsp) = 0x%llx  x26(allocptr) = 0x%llx\n",
                        (unsigned long long)state.__x[25], (unsigned long long)state.__x[26]);
                fprintf(stderr, "    x28(rcontext) = 0x%llx\n", (unsigned long long)state.__x[28]);
                /* Dump a few instructions around PC */
                unsigned int *pc_ptr = (unsigned int *)(uintptr_t)state.__pc;
                fprintf(stderr, "    Code around PC:\n");
                for (int i = -4; i <= 4; i++) {
                    fprintf(stderr, "      [%+d] %08x%s\n", i*4, pc_ptr[i],
                            i == 0 ? " <-- PC" : "");
                }
                /* Dump stack around SP */
                unsigned long long *sp_ptr = (unsigned long long *)(uintptr_t)state.__sp;
                fprintf(stderr, "    Stack around SP:\n");
                for (int i = 0; i < 16; i++) {
                    fprintf(stderr, "      [sp+%d] = 0x%llx\n", i*8, sp_ptr[i]);
                }
            } else {
                fprintf(stderr, "  Failed to get thread state: %d\n", kr);
            }

            thread_resume(main_mach);
            abort();
        }
        prev = cv;
        /* Tight polling - no sleep, max detection speed */
    }
    return NULL;
}

static void dbg_start_cursor_monitor(void) {
    dbg_main_thread = pthread_self();
    dbg_monitor_active = 1;
    pthread_t mon;
    pthread_create(&mon, NULL, dbg_cursor_monitor, (void *)dbg_fasl_cursor_addr);
    pthread_detach(mon);
    fprintf(stderr, "DBG: cursor monitor thread started, polling %p\n", dbg_fasl_cursor_addr);
}
#endif

ssize_t
lisp_read(int fd, void *buf, size_t count)
{
  ssize_t result = read(fd,buf,count);
#ifdef ARM64
  {
    static int read_trace_count = 0;
    read_trace_count++;
    if (read_trace_count <= 50 || result <= 0) {
      off_t pos = lseek(fd, 0, SEEK_CUR);
      fprintf(stderr, "DBG lisp_read[%d]: fd=%d buf=%p count=%zu result=%zd pos_after=%lld\n",
              read_trace_count, fd, buf, count, result, (long long)pos);
    }
    /* Track the FASL buffer cursor location (8 bytes before buf) */
    if (count == 2048 && result > 0 && read_trace_count <= 3) {
      dbg_fasl_cursor_addr = (void *)((char *)buf - 8);
      dbg_fasl_cursor_expected = *(unsigned long long *)dbg_fasl_cursor_addr;
      fprintf(stderr, "DBG cursor_addr=%p cursor_val=%016llx\n",
              dbg_fasl_cursor_addr, dbg_fasl_cursor_expected);
      /* Start monitor immediately when cursor addr is known */
      dbg_start_cursor_monitor();
    }
    /* Check cursor on every call */
    if (dbg_fasl_cursor_addr) {
      unsigned long long cv = *(unsigned long long *)dbg_fasl_cursor_addr;
      if (cv != 0 && cv < 0x10000) {
        fprintf(stderr, "DBG CURSOR CORRUPTED! addr=%p val=%016llx (sp=%p)\n",
                dbg_fasl_cursor_addr, cv, __builtin_frame_address(0));
      }
    }
  }
#endif
  return result;
}

ssize_t
lisp_write(int fd, void *buf, size_t count)
{
  return write(fd,buf,count);
}

int
lisp_open(char *path, int flags, mode_t mode)
{
  return open(path,flags,mode);
}

int
lisp_fchmod(int fd, mode_t mode)
{
  return fchmod(fd,mode);
}

int64_t
lisp_lseek(int fd, int64_t offset, int whence)
{
  int64_t result;
#ifdef LINUX
  result = lseek64(fd,offset,whence);
#else
  result = lseek(fd,offset,whence);
#endif
#ifdef ARM64
  /* Bug 162 diagnostic: if dbg_force_fasl_lseek is set, return 0 for
     SEEK_CUR/offset=0 (fd-tell) so %simple-fasl-set-file-pos always
     uses lseek instead of the cursor-incf shortcut. */
  {
    extern int dbg_force_fasl_lseek;
    if (dbg_force_fasl_lseek && whence == SEEK_CUR && offset == 0) {
      result = 0;
    }
  }
#endif
#ifdef ARM64
  {
    extern volatile void *dbg_fasl_cursor_addr;
    static int lseek_trace_count = 0;
    static int dbg_cursor_trap_armed = 0;
    lseek_trace_count++;
    if (lseek_trace_count <= 50) {
      fprintf(stderr, "DBG lisp_lseek[%d]: fd=%d offset=%lld whence=%d result=%lld",
              lseek_trace_count, fd, (long long)offset, whence, (long long)result);
      if (dbg_fasl_cursor_addr) {
        unsigned long long cv = *(unsigned long long *)dbg_fasl_cursor_addr;
        fprintf(stderr, " cursor=%016llx", cv);
        if (cv != 0 && cv < 0x10000) {
          fprintf(stderr, " ***CORRUPT***");
        }
      }
      fprintf(stderr, "\n");
    }
    /* Bug 162: cursor_trap_armed is now set by the monitor start in lisp_read */
  }
#endif
  return result;
}

int
lisp_close(int fd)
{
  return close(fd);
}

int
lisp_ftruncate(int fd, off_t length)
{
  return ftruncate(fd,length);
}

int
lisp_stat(char *path, void *buf)
{
  return stat(path,buf);
}

int
lisp_fstat(int fd, void *buf)
{
  return fstat(fd,buf);
}

int
lisp_lstat(char *path, void *buf)
{
  return lstat(path, buf);
}

int
lisp_futex(int *uaddr, int op, int val, void *timeout, int *uaddr2, int val3)
{
#ifdef LINUX
  return syscall(SYS_futex,uaddr,op,val,timeout,uaddr2,val3);
#else
  errno = ENOSYS;
  return -1;
#endif
}

DIR *
lisp_opendir(char *path)
{
  return opendir(path);
}

struct dirent *
lisp_readdir(DIR *dir)
{
  return readdir(dir);
}

int
lisp_closedir(DIR *dir)
{
  return closedir(dir);
}

int
lisp_pipe(int pipefd[2])
{
  return pipe(pipefd);
}

int
lisp_gettimeofday(struct timeval *tp, void *tzp)
{
  return gettimeofday(tp, tzp);
}

int
lisp_sigexit(int signum)
{
  signal(signum, SIG_DFL);
  return kill(getpid(), signum);
}

#ifdef ANDROID_NEEDS_SIGALTSTACK
/* I for one welcome our new Android overlords. */
#ifndef __NR_sigaltstack
#define __NR_sigaltstack		(__NR_SYSCALL_BASE+186)
#endif
int
sigaltstack(stack_t *in, stack_t *out)
{
  return syscall(__NR_sigaltstack,in,out);
}
#endif

char *
lisp_realpath(const char *file_name, char *resolved_name)
{
  return realpath(file_name, resolved_name);
}
