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

/* Debug global: address of FASL buffer cursor (8 bytes before data area) */
#ifdef ARM64
volatile void *dbg_fasl_cursor_addr = NULL;
volatile unsigned long long dbg_fasl_cursor_expected = 0;
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
      /* Use lldb to set: watchpoint set expression -w write -- (long long *)0x<cursor_addr> */
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
  {
    extern volatile void *dbg_fasl_cursor_addr;
    static int lseek_trace_count = 0;
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
