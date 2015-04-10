/*	$Id: OakFiles.c,v 1.12 1999/10/03 11:47:46 ooc-devel Exp $	*/
/*  Oakwood compliant file access.
    Copyright (C) 1997, 1998  Michael van Acken, Juergen Zimmermann

    This module is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public License
    as published by the Free Software Foundation; either version 2 of
    the License, or (at your option) any later version.

    This module is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with OOC. If not, write to the Free Software Foundation,
    59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/
#include "__oo2c.h"
#define _POSIX_SOURCE  /* file uses POSIX.1 functions */

#include <fcntl.h>
#include <errno.h>
#include <stdio.h>
#include <unistd.h> 
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#if TIME_WITH_SYS_TIME
# include <sys/time.h>
# include <time.h>
#else
# if HAVE_SYS_TIME_H
#  include <sys/time.h>
# else
#  include <time.h>
# endif
#endif

#ifndef O_BINARY  /* be kind to MS-DOG based systems */
#define O_BINARY 0
#endif

#include "__config.h"
#include "__mini_gc.h"
#include "OakFiles.h"
#include "Termination.h"

#if USE_GC
#ifdef __cplusplus
  extern "C" {
#endif
typedef void (*GC_finalization_proc)(void *obj, void *client_data);
extern void GC_register_finalizer(void *obj, GC_finalization_proc fn, void *cd, GC_finalization_proc *ofn, void **ocd);

static void finalize(void *obj, void *client_data);
#ifdef __cplusplus
  }  /* end of extern "C" */
#endif
#endif


/* constants from Files.Mod */
#define largeBlock 512
#define sizeBuffer (4*largeBlock)
#define maxFilenameLen 256

typedef CHAR (* FileName);

static int maxFdUsed = 10; /* max. number of physical files used */
static OakFiles__File openFiles = NULL; /* there are no files at startup */
static int fdInUse = 0; /* no fd's used by this module at startup*/
static int swapBytes = 0; /* do not swap bytes on write */
BOOLEAN OakFiles_permanentClose = 0;


static _ModId _mid;

/* module descriptor */
static const struct {
  int length;
  void* pad;
  const char name[9];
} _n0 = {9, NULL, {"OakFiles"}};
static struct _MD OakFiles__md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const unsigned char*)_n0.name, 
    -1, 
    NULL
  }
};




static void CreateTmpName(CHAR *name) {
/* create a name for a temporary file */
  CHAR *tmp = NULL;
  
  tmp = (CHAR*)tmpnam(NULL);
  _string_copy(name, tmp, maxFilenameLen);
}


static void ClearBuffer(OakFiles__Buffer *buf) {
  buf->start = 0;
  buf->end = 0;
  buf->read = 1;
}

static OakFiles__File NewFile(const CHAR *name) {
/* Allocate memory for a new File structure and initialize it. */
  OakFiles__File newfile;
  
  newfile = (OakFiles__File)GC_malloc_atomic(sizeof(OakFiles__FileDesc));
#if USE_GC
  {
    GC_finalization_proc ofn;
    void *ocd;
    
    GC_register_finalizer(newfile,finalize,NULL,&ofn,&ocd);
  }
#endif

  newfile->next = NULL;
  newfile->fd = -1;

  _string_copy(newfile->name, name, maxFilenameLen);
  CreateTmpName(newfile->tmpn);
  newfile->flagValid = 0;
  newfile->flagRead = 0;
  newfile->flagWrite = 0;
  newfile->flagMark = 0;
  newfile->flagReg = 0;
  newfile->flagKeepFd = 0;
  newfile->pos = -1;

  ClearBuffer(&(newfile->buffer));
  
  return newfile;
}

static void DeallocateFileDesc(OakFiles__File file) {
/* Close the file associated with 'file' and release 'fd' */
  if (file->flagValid == 1) {
    int res;
    do
      res = close(file->fd);
    while ((res != 0) && (errno == EINTR));
    
    file->fd = -1;
    file->flagValid = 0;
    file->flagRead = 0;
    file->flagWrite = 0;
    file->flagMark = 0;
    fdInUse--;
  }
}

static void FreeFileDesc(void);

static int GetFileDesc(OakFiles__File file, int newfile) {
  /* allocate a file descriptor for 'file'.
    'newfile' reflects the open mode:
     1: Files.New (create new file)
     0: Files.Open (open existing file)
  */
  int fd = -1;
  FileName fn = NULL;

/* Have a look on the number of file descriptors
  we have allocated.
  If we have already 'maxFdUsed' file descriptors,
  then try to release some of them */
  
  if (fdInUse == maxFdUsed)
    FreeFileDesc();
  
/* reset the state of the file to be opened */  
  file->flagValid = 0;
  file->flagMark = 0;
  file->flagRead = 0;
  file->flagWrite = 0;
  
  if (file->flagReg == 1)
    /* file is registered, i.e. use the 'name' field to determine
         the physical file */
    fn = file->name;
  else
    /* file was not yet registered, so use the 'tmpn' field
         as the name of the physical file */
    fn = file->tmpn;
  
  if (newfile == 1) {
    /* Create a new file. The Unix permissions for the new file are
      set to rw-rw-rw */
    do
      fd = open((char*)fn,(O_CREAT|O_TRUNC|O_RDWR|O_BINARY),
		(S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP|S_IROTH|S_IWOTH));
    while ((fd == -1) && (errno == EINTR));
    
    if ((fd == -1) && ((errno == EMFILE) || (errno == ENFILE)) && (fdInUse != 0)) {
      /* close one file and try again */
      FreeFileDesc();
      return GetFileDesc(file,newfile);
    } else if (fd == -1) {
      return 0;
    } else {
      file->fd = fd;
      file->flagValid = 1;
      file->flagRead = 1;
      file->flagWrite = 1;
    }
  } else {
    /* try to open the file for reading/writing */
    do
      fd = open((char*)fn,(O_RDWR|O_BINARY));
    while ((fd == -1) && (errno == EINTR));
    
    if ((fd == -1) && ((errno == EMFILE) || (errno == ENFILE)) && (fdInUse != 0)) {
      FreeFileDesc();
      return GetFileDesc(file,newfile);
    } else if (fd != -1) {
      file->fd = fd;
      file->flagValid = 1;
      file->flagRead = 1;
      file->flagWrite = 1;
    } else { 
      /* Open failed for reading/writing, so we try to open the file
	 just for reading */
      do
        fd = open((char*)fn,(O_RDONLY|O_BINARY)); 
      while ((fd == -1) && (errno == EINTR));
      
      if ((fd == -1) && ((errno == EMFILE) || (errno == ENFILE)) && (fdInUse != 0)) {
        FreeFileDesc();
        return GetFileDesc(file,newfile);
      } else if (fd != -1) {
        file->fd = fd;
        file->flagValid = 1;
        file->flagRead = 1;
        file->flagWrite = 0;
      } else {
        return 0;
      }
    }
  }
  fdInUse++;
  lseek(file->fd,file->pos,SEEK_SET);
  return 1;
}


static void AllocateFileDesc(OakFiles__File file) {
  if (file->flagValid == 1)
    file->flagMark = 0; /* touch */
  else if (GetFileDesc(file,0) == 0) {
    fprintf(stderr,"[Files] Failed to reopen file %s\n",file->name);
    _halt(0);
  }
}


static void FreeFileDesc(void) {
  OakFiles__File walk = openFiles;
  do {
    if ((walk->flagValid == 1) && (walk->flagKeepFd == 0)) {
      if (walk->flagMark == 1) {
	DeallocateFileDesc(walk);
	openFiles = walk;
	return;
      } else {
	walk->flagMark = 1;
      }
    }
    walk = walk->next;
  } while (walk != openFiles);
  FreeFileDesc();
}


static void InsertFile(OakFiles__File file) {
  if (openFiles == NULL) {
    openFiles = file;
    file->next=file;
  } else {
    OakFiles__File oldEnd = openFiles;
    
    while (oldEnd->next != openFiles) {
      oldEnd = oldEnd->next;
    }
    
    oldEnd->next = file;
    file->next = openFiles;
  }
}


#if USE_GC
static BOOLEAN StillInUse(OakFiles__File file)
{
  OakFiles__File walk = openFiles;

  while ((walk != NULL) && (walk != file) && (walk->next != openFiles))
    walk = walk->next;
  return (file == walk);
}
#endif

static void RemoveFile(OakFiles__File file) {
  DeallocateFileDesc(file);
  if (openFiles != NULL) {
    if (file->next == file) {
      openFiles = NULL;
    } else {
      OakFiles__File walk = openFiles;
      
      while ((walk->next != file) && (walk->next != openFiles)) {
	walk = walk->next;
      }
      
      walk->next = file->next;
      if (file == openFiles) {
	openFiles = file->next;
      }
    }
  } else {
    fprintf(stderr,"Unbalanced Close on Files\n");
  }
}


static LONGINT WriteToFile(OakFiles__File f, LONGINT pos, BYTE *adr, LONGINT n) {
  /* WriteToFile (f, pos, adr, n) writes the first n bytes starting at
    memory address adr to file f at position pos.
    f.pos is updated accordingly.
    Result is 0 on success and the number of bytes that could
    not be written on failure. */
  int res;
  
  AllocateFileDesc (f);
  if (f->flagWrite == 1)  /* fd is valid */ {
    res = lseek (f->fd, pos, SEEK_SET);
    do
      res = write (f->fd, adr, n);
    while ((res == -1) && (errno == EINTR));
    if (res == -1)  /* write error */
      res = 0;
    f->pos = pos+res;
    return (n-res);
  } else {
    return n;
  }
}

static LONGINT ReadFromFile(OakFiles__File f, LONGINT pos, BYTE *adr, LONGINT n) {
  /* ReadFromFile (f, pos, buf, n) reads the first n bytes at
    position pos from file f and stores them at memory address adr.
    f.pos is updated accordingly.
    Result is 0 on success and the number of bytes that could
    not be read on failure. */
  long int res;
  
  AllocateFileDesc (f);
  if (f->flagRead == 1) /* fd is valid */ {
    res = lseek (f->fd, pos, SEEK_SET);
    do
      res = read (f->fd, adr, n);
    while ((res == -1) && (errno == EINTR));
    if (res == -1) /* read error */
      res = 0;
    
    f->pos = pos+res;
    return (n-res);
  } else {
    return n;
  }
}

static void Flush(OakFiles__File f) {
  LONGINT res;
  
  if ((f->buffer.read == 0) && (f->buffer.end != f->buffer.start)) {
    /* write buffer to file if necessary */
    res = WriteToFile(f,f->buffer.start,&(f->buffer.data[0]),(f->buffer.end - f->buffer.start));
    f->buffer.end = f->buffer.start; /* clear buffer */
  }
}


static void SwapOrder(BYTE x[], LONGINT len) {
  if (swapBytes) {
    LONGINT i,j;
    BYTE c;
    /* swap the bytes */
    i=0; j=len-1;
    while (i < j) {
      c=x[i]; x[i]=x[j]; x[j]=c;
      i++; j--;
    }
  }
}

static void InitSwap(BYTE x[]) {
  swapBytes=(x[0] != 1);
/*
  if (swapBytes)
    fprintf(stderr,"OakFiles.InitSwap: big endian system\n");
  else
    fprintf(stderr,"OakFiles.InitSwap: little endian system\n");
*/
}




OakFiles__File OakFiles_Base(struct OakFiles__Rider *r) {
  if (r != NULL)
    return r->file;
  else
    return NULL;
}

static void CloseDown(OakFiles__File f) {
/* CloseDown (f) writes back the file buffers of f. The file is no more
   accessible by its handle f or the struct OakFiles__Riders positioned on it. */
  INTEGER res;

#if USE_GC
  if (StillInUse(f)) {
#endif
  Flush(f);
  DeallocateFileDesc(f);
  /* remove it from the internal tracking list */
  RemoveFile(f);
  if (f->flagReg == 0)
  /* File was not registered, so delete the temporary file. */
  OakFiles_Delete(f->tmpn, &res);
#if USE_GC
  }
#endif
}

void OakFiles_Close(OakFiles__File *f) {
/* Close (f) writes back the file buffers of f. The file is still accessible by
  its handle f and the struct OakFiles__Riders positioned on it. If a file is not modified it
  is not necessary to close it.
  
  Note: The above holds only for permanentClose=0, otherwise the buffers
  are flushed and the file handle is deallocated (and `f' is set to NIL).
  All struct OakFiles__Riders on this file will become invalid.  This behaviour and the
  variable permanentClose are not part of the Oakwood guidelines. */
  Flush(*f);
  if (OakFiles_permanentClose) {
    CloseDown (*f);
#if USE_GC
    {
      GC_finalization_proc ofn;
      void *ocd;
      
      GC_register_finalizer(*f,(GC_finalization_proc)NULL,NULL,&ofn,&ocd);
    }
    GC_free(*f);
#else
    free(*f); 
#endif
  } else {
    DeallocateFileDesc (*f);
  }
}


void OakFiles_Delete(const CHAR *name, INTEGER *res) {
  *res = (-unlink((const char*)name));
}

int get_o2time (long int sec, LONGINT *t, LONGINT *d) {
  time_t clock;
  struct tm *timestamp;
  
  clock = sec;
  timestamp = localtime(&clock);
  if (timestamp != NULL) {
    (*t) = (timestamp->tm_hour * 4096) +
         (timestamp->tm_min * 64) +
         (timestamp->tm_sec);
    (*d)=((timestamp->tm_year + 1900) * 512) +
         ((timestamp->tm_mon+1) * 32) +
         (timestamp->tm_mday);
    return 0;
  }
  else
    return -1;
}

void OakFiles_GetDate(OakFiles__File f, LONGINT *t, LONGINT *d) {
/* GetDate (f, t, d) returns the time t and date d of the
   last modification of file f.
   The encoding is:
   hour = t DIV 4096; minute = t DIV 64 MOD 64; second = t MOD 64;
   year = d DIV 512; month = d DIV 32 MOD 16; day = d MOD 32. */
  struct stat attr;
  int res;
  
  AllocateFileDesc(f);
  res = fstat(f->fd,&attr);

  if (res == 0) {
    if (get_o2time(attr.st_mtime,t,d) != 0) {
      (*t)=0;
      (*d)=0;
    }
  } else {
    (*t)=0;
    (*d)=0;
  }  
}


LONGINT OakFiles_Length(OakFiles__File f) {
  int res;
  struct stat attr;
  FileName name;

  if (f->flagReg)
    name = f->name;
  else
    name = f->tmpn;
  
  res = stat ((char*)name, &attr);
  if (res != 0)
    return -1;
  else
    return attr.st_size;
}


OakFiles__File OakFiles_New(const CHAR *name) {
  OakFiles__File f = NULL;
  
  f = NewFile(name);
  
  if (GetFileDesc(f,1) == 1) {
    InsertFile(f);
    return f;
  } else {
    fprintf(stderr,"OakFiles.New: Could not create %s for read/write\n",f->tmpn);
    return NULL;
  }
}


OakFiles__File OakFiles_Old(const CHAR *name) {
  OakFiles__File f = NULL;

  f = NewFile(name);
  f->flagReg = 1;

  if (GetFileDesc(f,0) == 1) {
    InsertFile(f);
    return f;
  } else {
    return NULL;
  }
}


LONGINT OakFiles_Pos(struct OakFiles__Rider *r) {
  if (r != NULL)
    return r->pos;
  else
    return -1;
}

/*
void OakFiles_Purge(OakFiles__File f) {
  int res;
  
  AllocateFileDesc(f);
  res = ftruncate(f->fd,0);
  ClearBuffer(&(f->buffer));
}
*/
void OakFiles_Purge(OakFiles__File f)
{
   int fd;
   FileName fn= NULL;

   DeallocateFileDesc (f); /* give up old file descriptor */
   ClearBuffer(&(f->buffer)); /* clear the buffer */

   if (f->flagReg) {
      /* file is registered, i.e. use the 'name' field to determine
	 the physical file */
      fn = f->name;
   } else {
      /* file was not yet registered, so use the 'tmpn' field
	 as the name of the physical file */
      fn = f->tmpn;
   }
   
   do {
      fd = open((char*)(f->name),(O_TRUNC|O_RDWR|O_BINARY),
		(S_IRUSR|S_IWUSR));
   } while ((fd == -1) && (errno == EINTR));
   
   if (fd == -1) {
     fprintf(stderr,"[Files.Purge] failed on file %s\n",f->name);
   } else {
     close (fd);
   }

   if (!GetFileDesc(f,0)) {
     fprintf(stderr,"[Files.Purge] failed on file %s\n",f->name);
   }
   
   f->pos=-1;
}

void OakFiles_ReadBytes(struct OakFiles__Rider *r, BYTE *x, LONGINT n) {
  OakFiles__File f;
  LONGINT n0;
  
  f = r->file;
  if (f->buffer.read && (f->buffer.start <= r->pos) && (r->pos+n <= f->buffer.end)) {  
     /* all required bytes are in the file buffer */
    memcpy(x, &(f->buffer.data[r->pos-f->buffer.start]), n);
    r->pos+= n;
    r->res = 0;
  } else if (n < largeBlock) { /* block small enough to update buffer */
    /* refill buffer */
    Flush (f);
    n0 = sizeBuffer - ReadFromFile (f, r->pos, &(f->buffer.data[0]), sizeBuffer);
    /* n0 is the number of bytes that were actually read into buffer */
    f->buffer.start = r->pos;
    f->buffer.end = r->pos+n0;
    /* not more than n0 bytes can be taken from the buffer */
    if (n > n0) {
      r->res = n-n0;
      n = n0;
      r->eof = 1;
    } else {
      r->res = 0;
    }
    memcpy(x, f->buffer.data, n);
    r->pos += n;
  } else {
    /* bytes not in buffer and block too large to use buffer */
    Flush (f);
    r->res = ReadFromFile (r->file, r->pos, x, n);
    if (r->res != 0) { /* couldn't read n bytes: probably end of file */
      r->eof = 1;
    }
    r->pos = f->pos;
  }
}

void OakFiles_WriteBytes(struct OakFiles__Rider *r, BYTE *x, LONGINT n) {
  OakFiles__File f;

  f = r->file;
  if ((!f->buffer.read) &&
     (f->buffer.start <= r->pos) && (r->pos <= f->buffer.end) &&
     (r->pos+n <= f->buffer.start+sizeBuffer)) { /* bytes fit into buffer */
    memcpy(&(f->buffer.data[r->pos-f->buffer.start]), x, n);
    r->pos += n;
    r->res = 0;
    if (r->pos > f->buffer.end) {
      f->buffer.end = r->pos;
    }
  } else if (n < largeBlock) {
    /* block small enough to put it into the buffer */
    Flush (f);
    f->buffer.read = 0;
    f->buffer.start = r->pos;
    r->pos += n;
    r->res = 0;
    f->buffer.end = r->pos;
    memcpy(f->buffer.data, x, n);
  } else {
    /* block to large, write directly to file */
    Flush (f);
    r->res = WriteToFile (f, r->pos, x, n);
    r->pos = f->pos;
  }
}

static OakFiles__File regFile = NULL;

void OakFiles_Register(OakFiles__File f) {
/* Register (f) enters the file f into the directory together with the name
   provided in the operation New that created f. The file buffers are
   written back. Any existing mapping of this name to another file is
   overwritten. */
#define bufSize  16384
  LONGINT oldpos;
  INTEGER dummy;
  int res;
  BYTE buffer[bufSize];
  BOOLEAN err;
  LONGINT n;
  
  if (regFile == NULL) {
    regFile = NewFile(f->name);
    regFile->flagReg = 1;
  }

  if (f->flagReg == 0) {
    Flush(f);
    oldpos = f->pos;
    _string_copy(regFile->name, f->name, maxFilenameLen);
    regFile->fd = -1;
    regFile->pos = 0;
    regFile->buffer.start = 0;
    regFile->buffer.end = 0;

    /* try to open old file (whose contents are to be copied into to
      registered file) and the new file, which will reside in the
      registered file's place */
    AllocateFileDesc(f);
    f->flagKeepFd = 1; /* ensure that f keeps it's fd */
    if (GetFileDesc(regFile,1) == 1) {
      /* new file could be opened, so 'f' becomes registered */
      InsertFile(regFile);
      f->flagReg = 1;
    }
    f->flagKeepFd = 0;  /* make f's fd available again */

    if ((regFile->flagValid == 0) ||
          (regFile->flagWrite == 0) ||
          (f->flagValid == 0) ||
          (f->flagRead == 0)) {
      fprintf(stderr,"[Files] Unable to register file %s\n",(char*)regFile->name);
      _halt(0);
    }

    /* copy the whole file */
    /* set both positions to start of file */
    res = lseek(f->fd,0,SEEK_SET);
    res = lseek(regFile->fd,0,SEEK_SET);
    err = 0;
    while(1) {
      do
	n = read (f->fd, buffer, bufSize);
      while ((n == -1) && (errno == EINTR));
      if (n == -1) {
	err = 1;
	goto _loopend;
      }
      do
	n = write (regFile->fd, buffer, n);
      while ((n == -1) && (errno == EINTR));
      if (n == -1) {
	err = 1;
	goto _loopend;
      }
      if (n != bufSize)
	goto _loopend;
    }
    _loopend:
    if (err == 1) {
      OakFiles_Delete(f->name,&dummy); /* an error occured during registration, remove file */
      fprintf(stderr,"*** Warning: [Files] Unable to register file %s\n",regFile->name);
      f->pos = oldpos; /* set the old position */
      f->flagReg =0;
    } else {
      CloseDown(regFile); /* Remove 'regFile' from tracking list */
      OakFiles_Delete(f->tmpn,&dummy); /* delete the old temporary file */
      DeallocateFileDesc(f);
      f->pos = oldpos; /* set the old position */
      AllocateFileDesc(f);  /* try to get a file descriptor for 'f' */
    }
  }
}

void OakFiles_Rename(const CHAR *old, const CHAR *newname, INTEGER *res) {
  *res = -(rename((const char*)old,(const char*)newname));
}

void OakFiles_Set(struct OakFiles__Rider *r, OakFiles__File f, LONGINT pos)
{
  if (r != NULL) {
    r->file=f;
    AllocateFileDesc(f);
    Flush(f);
    r->eof = 0;
    r->pos = pos;
  } else {
    fprintf(stderr,"OakFiles.Set: struct OakFiles__Rider not valid\n");
  }
}

static void WriteBytesSwap(struct OakFiles__Rider *r, BYTE *x, LONGINT n) {
  SwapOrder(x,n);
  OakFiles_WriteBytes(r,x,n);
}

static void ReadBytesSwap(struct OakFiles__Rider *r, BYTE *x, LONGINT n) {
  OakFiles_ReadBytes(r,x,n);
  SwapOrder(x,n);
}



void OakFiles_Write (struct OakFiles__Rider *r, BYTE x) {
/* Write (r, x) writes the byte x to struct OakFiles__Rider r and advances r accordingly. */
  if ((r->file->buffer.read == 0) &&
     (r->file->buffer.start <= r->pos) &&
     (r->pos <= r->file->buffer.end) &&
     (r->file->buffer.end < (r->file->buffer.start+sizeBuffer))) {
    /* previous operation was a write, the current byte is in the buffer
      and the buffer won't overflow is a byte is appended */
    r->file->buffer.data[(r->pos - r->file->buffer.start)] = x;
    r->pos++;
    if (r->file->buffer.end < r->pos)
      r->file->buffer.end = r->pos;
  } else {
    OakFiles_WriteBytes(r,&x,sizeof(BYTE));
  }
}

void OakFiles_WriteBool (struct OakFiles__Rider *r, BOOLEAN x) {
  if (x == 1)
    OakFiles_Write(r,'\001');
  else
    OakFiles_Write(r,'\000');
}

void OakFiles_WriteInt (struct OakFiles__Rider *r, INTEGER x) {
  WriteBytesSwap(r,(BYTE*)&x,sizeof(INTEGER));
}

void OakFiles_WriteLInt (struct OakFiles__Rider *r, LONGINT x) {
  WriteBytesSwap(r,(BYTE*)&x,sizeof(LONGINT));
}

void OakFiles_WriteLReal (struct OakFiles__Rider *r, LONGREAL x) {
  WriteBytesSwap(r,(BYTE*)&x,sizeof(LONGREAL));
}

void OakFiles_WriteNum (struct OakFiles__Rider *r, LONGINT x) {
  LONGINT m;

  while ((x< -64) || (x >63))
  {
    _mod(m, x, 128, LONGINT);
    OakFiles_Write(r, (CHAR)(m+128));
    _div(x, x, 128, LONGINT);
  }
  _mod(m, x, 128, LONGINT);
  OakFiles_Write(r,(CHAR)m);
}

void OakFiles_WriteReal (struct OakFiles__Rider *r, REAL x) {
  WriteBytesSwap(r,(BYTE*)&x,sizeof(REAL));
}

void OakFiles_WriteSet (struct OakFiles__Rider *r, SET x) {
  WriteBytesSwap(r,(BYTE*)&x,sizeof(SET));
}

void OakFiles_WriteString (struct OakFiles__Rider *r, const CHAR *x) {
  LONGINT i=-1;
  do {
    i++;
    OakFiles_Write(r,(BYTE)x[i]);
  } while (x[i] != '\000');
}

void OakFiles_Read (struct OakFiles__Rider *r, BYTE *x) {
  OakFiles_ReadBytes(r,x,sizeof(BYTE));
}


void OakFiles_ReadBool (struct OakFiles__Rider *r, BOOLEAN *x) {
  BYTE y;
  OakFiles_Read(r,&y);
  if (y == 1)
    *x=1;
  else
    *x=0;
}

void OakFiles_ReadInt (struct OakFiles__Rider *r, INTEGER *x) {
  ReadBytesSwap(r,(BYTE*)x,sizeof(INTEGER));
}

void OakFiles_ReadLInt (struct OakFiles__Rider *r, LONGINT *x) {
  ReadBytesSwap(r,(BYTE*)x,sizeof(LONGINT));
}

void OakFiles_ReadLReal (struct OakFiles__Rider *r, LONGREAL *x) {
  ReadBytesSwap(r,(BYTE*)x,sizeof(LONGREAL));
}

void OakFiles_ReadNum (struct OakFiles__Rider *r, LONGINT *x) {
  SHORTINT s = 0;
  CHAR ch;
  LONGINT n = 0;

  OakFiles_Read(r, &(ch));
  while (((INTEGER)ch >= 128) && (r->eof == 0)) {
    n = n + (((INTEGER) ch-128) << s);
    s = s+7;
    OakFiles_Read(r, &(ch));
  }

  if (r->eof == 1) {
    r->res = 1; /* indicate error */
    (* x) = 0;  /* asure defined state */
    fprintf(stderr,"[Files.ReadNum] End of file reached in '%s'\n",(char*)r->file->name);
    /*    _halt(0);*/
  } else {
    INTEGER m, d;

    r->res = 0;
    _mod(m, (INTEGER)ch, 64, INTEGER);
    _div(d, (INTEGER)ch, 64, INTEGER);
    (* x) = n+((m-d*64) << s);
  }
}

void OakFiles_ReadReal (struct OakFiles__Rider *r, REAL *x) {
  ReadBytesSwap(r,(BYTE*)x,sizeof(REAL));
}

void OakFiles_ReadSet (struct OakFiles__Rider *r, SET *x) {
  ReadBytesSwap(r,(BYTE*)x,sizeof(SET));
}

void OakFiles_ReadString (struct OakFiles__Rider *r, CHAR *x) {
  LONGINT i = -1;
  do {
    i++;
    OakFiles_Read(r,&(x[i]));
  } while ((x[i] != '\000') && (r->eof == 0));


  if (r->eof == 1) {
    r->res = 1; /* indicate error */
    x[0] = '\000'; /* asure 'usable' state */
    fprintf(stderr,"[Files.ReadString] End of file reached in '%s'\n",(char*)r->file->name);
/*    _halt(0); */
  } else {
    r->res = 0;
  }
}


#if USE_GC
static void finalize(void *obj, void *client_data)
{
  CloseDown((OakFiles__File)obj);
}
#endif


void Cleanup(void) {
  /* Closes all ever opened files which are still valid. */
  while (openFiles != NULL) {
    CloseDown(openFiles);
  }
}

void OakFiles_init (void) {
  INTEGER swapTest = 1;
  _mid = _register_module (&OakFiles__md.md, NULL);
  InitSwap((BYTE*)&swapTest);
  fdInUse = 0;
  Termination__RegisterProc(Cleanup);
}
