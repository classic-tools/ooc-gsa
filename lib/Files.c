/*	$Id: Files.c,v 1.17 2000/07/21 17:02:49 ooc-devel Exp $	*/
/*  Access to files and file attributes.
    Copyright (C) 1997-2000  Michael van Acken

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
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <string.h>
#include <utime.h>
#include <limits.h>

#include "__oo2c.h"
#include "__mini_gc.h"
#include "__StdTypes.h"
#include "__config.h"

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

/* the minimum number of temporary files supported by any system; GNU libc info
   says this is 25 */
#define TMP_MIN 25
/* prepare for the worst and assume that really just TMP_MIN temporary names
   are available; maintain a buffer of discarded names */
static char *tmp_name[TMP_MIN];

/* this is the currently active umask of the process; it is used by procedure
   Register */
static mode_t active_umask;

/* if the system imposes no limit on the length of a file name, choose an 
   arbitrary large value instead */
#ifndef PATH_MAX
#define PATH_MAX 2048
#endif


/* --- begin #include "Files.d" */
#include "Files.h"
#include "CharClass.h"
#include "LongStrings.h"
#include "Termination.h"

/* local definitions */
static Files__ErrorContext Files__errorContext;

/* function prototypes */

/* module and type descriptors */
static const struct {
  int length;
  void* pad;
  const char name[6];
} _n0 = {6, NULL, {"Files"}};
static struct _MD Files_md = {
  NULL, 
  &Kernel__ModuleDesc_td.td, 
  {
    NULL, 
    (const CHAR*)_n0.name, 
    -1, 
    NULL
  }
};

static const struct {
  int length;
  void* pad;
  const char name[9];
} _n1 = {9, NULL, {"FileDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[3];
} Files__FileDesc_tdb = {
  3, 
  NULL, 
  {
    &Channel__ChannelDesc_td.td, 
    &PosixFileDescr__ChannelDesc_td.td, 
    &Files__FileDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[8];
} _tb0 = {8, NULL, {
  (void*)PosixFileDescr__ChannelDesc_Length, 
  (void*)PosixFileDescr__ChannelDesc_GetModTime, 
  (void*)Files__FileDesc_NewReader, 
  (void*)Files__FileDesc_NewWriter, 
  (void*)PosixFileDescr__ChannelDesc_Flush, 
  (void*)Files__FileDesc_Close, 
  (void*)Channel__ChannelDesc_ClearError, 
  (void*)Files__FileDesc_Register
}};
struct _TD Files__FileDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Files__FileDesc_tdb.btypes,
    _tb0.tbprocs,
    (const CHAR*)_n1.name,
    &Files_md.md,
    2, 
    '0', '1',
    sizeof(Files__FileDesc),
    NULL
  }
};

static const struct {
  int length;
  void* pad;
  const char name[11];
} _n2 = {11, NULL, {"ReaderDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[3];
} Files__ReaderDesc_tdb = {
  3, 
  NULL, 
  {
    &Channel__ReaderDesc_td.td, 
    &PosixFileDescr__ReaderDesc_td.td, 
    &Files__ReaderDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[6];
} _tb1 = {6, NULL, {
  (void*)PosixFileDescr__ReaderDesc_Pos, 
  (void*)PosixFileDescr__ReaderDesc_Available, 
  (void*)PosixFileDescr__ReaderDesc_SetPos, 
  (void*)PosixFileDescr__ReaderDesc_ReadByte, 
  (void*)PosixFileDescr__ReaderDesc_ReadBytes, 
  (void*)Channel__ReaderDesc_ClearError
}};
struct _TD Files__ReaderDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Files__ReaderDesc_tdb.btypes,
    _tb1.tbprocs,
    (const CHAR*)_n2.name,
    &Files_md.md,
    2, 
    '0', '1',
    sizeof(Files__ReaderDesc),
    &Files__FileDesc_td.td
  }
};

static const struct {
  int length;
  void* pad;
  const char name[11];
} _n3 = {11, NULL, {"WriterDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[3];
} Files__WriterDesc_tdb = {
  3, 
  NULL, 
  {
    &Channel__WriterDesc_td.td, 
    &PosixFileDescr__WriterDesc_td.td, 
    &Files__WriterDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[6];
} _tb2 = {6, NULL, {
  (void*)PosixFileDescr__WriterDesc_Pos, 
  (void*)PosixFileDescr__WriterDesc_SetPos, 
  (void*)PosixFileDescr__WriterDesc_WriteByte, 
  (void*)PosixFileDescr__WriterDesc_WriteBytes, 
  (void*)Channel__WriterDesc_ClearError, 
  (void*)Files__WriterDesc_Truncate
}};
struct _TD Files__WriterDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Files__WriterDesc_tdb.btypes,
    _tb2.tbprocs,
    (const CHAR*)_n3.name,
    &Files_md.md,
    2, 
    '0', '1',
    sizeof(Files__WriterDesc),
    &Files__ReaderDesc_td.td
  }
};

static const struct {
  int length;
  void* pad;
  const char name[17];
} _n4 = {17, NULL, {"ErrorContextDesc"}};
static const struct {
  int length;
  void* pad;
  _Type btypes[4];
} Files__ErrorContextDesc_tdb = {
  4, 
  NULL, 
  {
    &Msg__ContextDesc_td.td, 
    &Channel__ErrorContextDesc_td.td, 
    &PosixFileDescr__ErrorContextDesc_td.td, 
    &Files__ErrorContextDesc_td.td
  }
};
static const struct {
  int length;
  void* pad;
  const void* tbprocs[1];
} _tb3 = {1, NULL, {
  (void*)Files__ErrorContextDesc_GetTemplate
}};
struct _TD Files__ErrorContextDesc_td = {
  NULL,
  &Types__TypeDesc_td.td,
  {
    Files__ErrorContextDesc_tdb.btypes,
    _tb3.tbprocs,
    (const CHAR*)_n4.name,
    &Files_md.md,
    3, 
    '0', '1',
    sizeof(Files__ErrorContextDesc),
    &Files__WriterDesc_td.td
  }
};

/* local strings */

/* --- end #include "Files.d" */


/* this variable holds a list of open files; it is used to remove any temporary
   files on program exit */
static Files__File open_files = NULL;

static _ModId _mid;


/* function definitions */


void Files__ErrorContextDesc_GetTemplate (Files__ErrorContext context, 
  Msg__Msg msg, Msg__LString templ, int templ_0d) {
  char *str;
  LONGINT res = msg->code;
  
  if (res == Files__channelClosed) {
    str = "File has been closed";
  } else if (res == Files__noReadAccess) {
    str = "No read permission for file";
  } else if (res == Files__noWriteAccess) {
    str = "No write permission for file";
  } else if (res == Files__closeError) {
    str = "Error while closing the file";
  } else if (res == Files__accessDenied) {
    str = "Failed to open file with requested access rights";
  } else if (res == Files__isDirectory) {
    str = "Can't get write access to directory file";
  } else if (res == Files__tooManyFiles) {
    str = "Too many open files at the moment";
  } else if (res == Files__noSuchFile) {
    str = "The named file does not exist";
  } else if (res == Files__directoryFull) {
    str = "Can't add new files to directory";
  } else if (res == Files__readOnlyFileSystem) {
    str = "File system is read-only";
  } else if (res == Files__invalidTime) {
    str = "Invalid modification time";
  } else if (res == Files__notOwner) {
    str = "Must be owner of file to change its modification time";
  } else if (res == Files__anonymousFile) {
    str = "Can't register anonymous file";
  } else if (res == Files__dirWriteDenied) {
    str = "Don't have write permission for directory";
  } else if (res == Files__fileError) {
    str = "Failed to open file";
  } else if (res == Files__nameTooLong) {
    str = "The file name or one of its components is too long";
  } else if (res == Files__notDirectory) {
    str = "A directory component of the file name exists, but isn't a directory";
  } else if (res == Files__linkLoop) {
    str = "Resolved too many symbolic links while looking up the file";
  } else {
    str = NULL;
  } 

  if (str) {
    _string_copy2l(templ, str, templ_0d);
    if (msg->attribList) {
      Msg__Attribute attr;
      LONGCHAR eol[2] = {(LONGCHAR)CharClass__eol, (LONGCHAR)0};
      LONGCHAR str16[Msg__sizeAttrName+1];
      
      /*LongStrings__Append(eol, 2, templ, templ_0d);*/
      attr = msg->attribList;
      while (attr) {
	LongStrings__Append(eol, 2, templ, templ_0d);
	_string_copy2l(str16, (char*)attr->name, strlen((char*)attr->name)+1);
	LongStrings__Append(str16, Msg__sizeAttrName+1, templ, templ_0d);
	_string_copy2l(str16, "=${", 4);
	LongStrings__Append(str16, Msg__sizeAttrName+1, templ, templ_0d);
	_string_copy2l(str16, (char*)attr->name, strlen((char*)attr->name)+1);
	LongStrings__Append(str16, Msg__sizeAttrName+1, templ, templ_0d);
	_string_copy2l(str16, "}", 2);
	LongStrings__Append(str16, Msg__sizeAttrName+1, templ, templ_0d);
	attr = attr->nextAttrib;
      }
    }
  } else {
    STATIC_TBCALL(PosixFileDescr,ErrorContextDesc,GetTemplate,context,
		  ((PosixFileDescr__ErrorContext)context,msg,templ,templ_0d));
  }
}

static void add_msg_attribute(Files__Result msg, const char* name, const char* value) {
  DYN_TBCALL(Msg,MsgDesc,SetStringAttrib,msg,
	     (msg, (const Msg__String)name, strlen(name)+1,
              Msg__GetStringPtr((CHAR*)value, strlen(value)+1)));
}

static Files__Result get_error(Msg__Code code, int use_errno, Files__File f) {
  Files__Result msg;
  
  msg = Msg__New((Msg__Context)Files__errorContext, code);
  if (use_errno) {
#if HAVE_STRERROR
    add_msg_attribute(msg, "errstr", strerror(errno));
#endif
    DYN_TBCALL(Msg,MsgDesc,SetIntAttrib,msg,
	       (msg, (const Msg__String)"errno", 6, (LONGINT)errno));
  }
  if (f) {
    if (f->tmpName) {
      add_msg_attribute(msg, "file_name", f->tmpName);
    } else if (f->name) {
      add_msg_attribute(msg, "file_name", f->name);
    }
  }

  return msg;
}


static Files__Result file_error(const char *name, const char *new_name) {
  /* if new_name != NULL: rename operation */
  Msg__Code code;
  Files__Result msg;
  
  switch (errno) {
  case EACCES:
    code = Files__dirWriteDenied;
    break;
  case EISDIR:
    code = Files__isDirectory;
    break;
  case EMFILE:
  case ENFILE: 
    code = Files__tooManyFiles;
    break;
  case ENOENT:
    code = Files__noSuchFile;
    break;
  case ENOSPC:
    code = Files__directoryFull;
    break;
  case EROFS:
    code = Files__readOnlyFileSystem;
    break;
  case ENAMETOOLONG:
    code = Files__nameTooLong;
    break;
  case ENOTDIR:
    code = Files__notDirectory;
    break;
#ifdef ELOOP
  case ELOOP:
    code = Files__linkLoop;
    break;
#endif
  case EPERM:
    code = Files__notOwner;
    break;
  default:
    code = Files__fileError;
  }
  
  msg = get_error(code, 1, NULL);
  if (new_name) {
    add_msg_attribute(msg, "old_name", name);
    add_msg_attribute(msg, "new_name", new_name);
  } else if (name) {
    add_msg_attribute(msg, "file_name", name);
  }
  
  return msg;
}

static void free_tmp_name (Files__File f) {
/* pre: f->tmpName != NULL */
  int i;
  
  /* try to find an unused slot in tmp_name */
  i = 0;
  while ((i < TMP_MIN) && tmp_name[i]) {
    i++;
  }
  if (i < TMP_MIN) {		/* store name for later use */
    tmp_name[i] = (char*)f->tmpName;
  } else {			/* discard file name */
    GC_free(f->tmpName);
  }
  f->tmpName = NULL;
  if(f->name) {
    GC_free(f->name);
    f->name = NULL;
  }
}

void Files__FileDesc_Register(Files__File f) {
  if (!f->open) {
    f->res = get_error(Files__channelClosed, 0, f);
  } else if (f->anonymous) {
    f->res= get_error(Files__anonymousFile, 0, f);
  } else {
    int res;
    
    /* flush file */
    DYN_TBCALL(Channel,ChannelDesc,Flush,f,((Channel__Channel)f));
    
    /* the temporary file has only write permissions for the user; now 
       add group and others permissions to the file as far as the umask 
       allows it */
    res = chmod((const char*)f->tmpName, 
		(S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP|S_IROTH|S_IWOTH) & 
		~active_umask);
    
    if (res != -1) {	/* rename file atomically */
      res = rename((const char*)f->tmpName, (const char*)f->name);
    }
    
    if (res == -1) {
      f->res = file_error((const char*)f->tmpName, (const char*)f->name);
    } else {
      free_tmp_name(f);
    }
  }
}

Files__Reader Files__FileDesc_NewReader(Files__File f) {
  Files__Reader r = NULL;

  if (!f->open) {
    f->res = get_error(Channel__channelClosed, 0, f);
  } else if (f->readable) {
    NEW_REC(r, Files__ReaderDesc);
    PosixFileDescr__InitReader ((PosixFileDescr__Reader)r, (PosixFileDescr__Channel)f);
  } else {
    f->res = get_error(Channel__noReadAccess, 0, f);
  }

  return r;
}

Files__Writer Files__FileDesc_NewWriter(Files__File f) {
  Files__Writer w = NULL;

  if (!f->open) {
    f->res = get_error(Channel__channelClosed, 0, f);
  } else if (f->writable) {
    NEW_REC(w, Files__WriterDesc);
    PosixFileDescr__InitWriter ((PosixFileDescr__Writer)w, (PosixFileDescr__Channel)f);
  } else {
    f->res = get_error(Channel__noWriteAccess, 0, f);
  }

  return w;
}

void Files__FileDesc_Close(Files__File f) {
  PosixFileDescr__ChannelDesc_Close ((PosixFileDescr__Channel)f);

  /* remove `f' from the list of open files */
  if (open_files == f) {
    open_files = f->next;
  } else {
    Files__File ptr = open_files;

    while (ptr->next != f) {
      ptr = ptr->next;
    }
    ptr->next = f->next;
  }

  /* delete temporary file and free its name */
  if (f->tmpName) {
    (void)unlink((const char*)f->tmpName);
    free_tmp_name(f);
  }
}

void Files__WriterDesc_Truncate(Files__Writer w, int newLength) {
  PosixFileDescr__Truncate ((PosixFileDescr__Writer)w->base, newLength);
}



static int open_file(const CHAR* name, int open_flags, int pflags) {
  int fd;

#ifdef O_BINARY  /* be kind to MS-DOG based systems */
  open_flags |= O_BINARY;
#endif

  do {
    fd = open((const char*)name, open_flags, pflags);
  } while ((fd == -1) && (errno == EINTR));
  return fd;
}
  

#define NO_ERROR ((fd == -2) || ((fd == -1) && (errno == EACCES)))
#define RD_FLAGS ((1<<Files__read) | (1<<Files__tryRead))
#define WR_FLAGS ((1<<Files__write) | (1<<Files__tryWrite))
#define MODE_OLD 0
#define MODE_NEW 1
#define MODE_TMP 2
#define MODE_TMP_GEN_NAME 3

static int call_open (const CHAR* name, SET flags, int mode, int *access_mode) {
  /* create a new file or open one; try to open the file first with read and 
     write, permissions, then just read, then just write; if everything fails
     report `access denied'; for temporary files the permissions on the file
     system are set to zero, i.e. even the user has no read/write permissions,
     except through the current file descriptor */
  int fd, open_flags, permissions;

  if (mode == MODE_TMP_GEN_NAME) {
    open_flags = O_CREAT|O_EXCL;
  } else if (mode == MODE_NEW) {
    /* get rid of any previous file, since open will use the permissions of
       the previous file otherwise; this would break New() if we don't have 
       the requested permissions for the existing file */
    if (flags & (RD_FLAGS|WR_FLAGS)) {
      (void)unlink((const char*)name);
    }
    open_flags = O_CREAT|O_TRUNC;
  } else if (mode == MODE_TMP) {
    open_flags = O_CREAT|O_TRUNC;
  } else {  /* MODE_OLD */
    open_flags = 0;
  }
  if (mode == MODE_NEW) {
    permissions = S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP|S_IROTH|S_IWOTH;
  } else {
    permissions = S_IWUSR;
  }

  fd = -2;
  if ((flags & RD_FLAGS) && (flags & WR_FLAGS)) {
    fd = open_file(name, open_flags|O_RDWR, permissions);
    if ((fd == -1) && (errno == EACCES) &&
	(flags & (1<<Files__read)) &&
	(flags & (1<<Files__write))) {
      return -3;
    }
    *access_mode = PosixFileDescr__readWrite;
  } 
  if (NO_ERROR && (flags & RD_FLAGS)) {
    fd = open_file(name, open_flags|O_RDONLY, permissions);
    if ((fd == -1) && (errno == EACCES) && (flags & (1<<Files__read))) {
      return -3;
    }
    *access_mode = PosixFileDescr__readOnly;
  }
  if (NO_ERROR && (flags & WR_FLAGS)) {
    fd = open_file(name, open_flags|O_WRONLY, permissions);
    if ((fd == -1) && (errno == EACCES) && (flags & (1<<Files__write))) {
      return -3;
    }
    *access_mode = PosixFileDescr__writeOnly;
  }
  if (NO_ERROR) {
    return -3;
  }

  return fd;
}

static CHAR* local_strdup (const CHAR* str) {
  /* strdup is a SVID function; it can't be used in this file */
  CHAR *new;
  new = (CHAR*)GC_malloc_atomic(strlen((const char*)str)+1);
  if (new) (void)strcpy((char*)new, (const char*)str);
  return new;
}

static Files__File create_file(const CHAR* name, SET flags, int mode,
			       Files__Result *res) {
/* Open the file `name' using the flags in `flags' that were initially passed 
   to New() or Tmp().  `mode' characterizes one of the four ways a file can
   be treated when opening it: old file, new file, temporary file, and 
   anonymous temporary file.  An error code is returned in `res'.  */
  int fd, access_mode;
  Files__File ch = NULL;
  char tname[PATH_MAX+16];
  
  if (strlen((const char*)name) > PATH_MAX) {
    *res = get_error(Files__nameTooLong, 0, NULL);
    add_msg_attribute(*res, "file_name", (const char*)name);
    return NULL;
  }

  if (mode == MODE_TMP_GEN_NAME) {
    /* lets try to find an unused name for our temporary file */
    int count = 0;
    
    do {
      /* repeat trying to open the file until an unused file is found, or
	 an error occured */
      if (count) {
	(void)sprintf(tname, "%s^%d", (const char*)name, count);
      } else {
	(void)sprintf(tname, "%s^", (const char*)name);
      }
      fd = call_open((const CHAR*)tname, flags, mode, &access_mode);
      count++;
    } while ((fd == -1) && (errno == EEXIST));
  } else {
    fd = call_open(name, flags, mode, &access_mode);
  }
  
  if (fd == -3) {
    /* couldn't get the requested access rights */
    *res = get_error(Files__accessDenied, 0, NULL);
    add_msg_attribute(*res, "file_name", name);
  } else if (fd == -1) {
    /* some other error */
    *res = file_error(name, NULL);
  } else {
    /* file was opened with the requested access rights */
    NEW_REC(ch, Files__FileDesc);
    *res = Channel__done;
    PosixFileDescr__Init((PosixFileDescr__Channel)ch, fd, access_mode);
    ch->next = open_files;
    if (mode == MODE_TMP_GEN_NAME) {
      ch->tmpName = local_strdup((const CHAR*)tname);
    } else {
      ch->tmpName = NULL;
    }
    ch->name = NULL;
    ch->anonymous = 0;
    open_files = ch;
  }

  return ch;
}

Files__File Files__New(const CHAR* file__ref, int file_0d, unsigned int flags, Files__Result *res) {
  return create_file(file__ref, flags, MODE_NEW, res);
}

Files__File Files__Old(const CHAR* file__ref, int file_0d, unsigned int flags, Files__Result *res) {
  return create_file(file__ref, flags, MODE_OLD, res);
}

Files__File Files__Tmp(const CHAR* file__ref, int file_0d, unsigned int flags, Files__Result *res) {
  Files__File ch = NULL;
  char new_name[L_tmpnam];
  char *tname;
  int i, anonymous;
  
  anonymous = (!file__ref[0]);

  if (anonymous) {
    /* first check if we have an unused name in stock */
    i = 0;
    while ((i < TMP_MIN) && !tmp_name[i]) {
      i++;
    }
    if (i < TMP_MIN) {
      /* this is our lucky day, we found an unused name */
      tname = tmp_name[i];
      tmp_name[i] = NULL;
    } else {
      /* there aren't any discarded names available right now; try to 
	 get a new one */
      tname = tmpnam(new_name);
      if (tname) tname = (char*)local_strdup((CHAR*)tname);
    }
  } else {
    tname = (char*)file__ref;
  }

  if (tname) {
    /* create file with minimal permissions; the permissions are extended
       upon registration if the umask allows it */
    ch = create_file((const CHAR*)tname, flags, 
		     file__ref[0]?MODE_TMP_GEN_NAME:MODE_TMP, res);
    if (ch) {
      ch->anonymous = anonymous;
      if (anonymous) {
	ch->tmpName = (CHAR*)tname;
      } else {
	ch->name = local_strdup(file__ref);
      }
    }
    return ch;
  } else {
    *res = get_error(Channel__noTmpName, 0, ch);
    return NULL;
  }
}

/* define the day count of the Unix epoch (Jan 1 1970 00:00:00 GMT) for the
   Time.TimeStamp format */
#define days_to_epoch 40587
#define end_of_epoch 65442
#define secs_per_day 86400

void Files__SetModTime(const CHAR* file__ref, int file_0d, const Time__TimeStamp *mtime__ref, Files__Result *fres) {
  if ((mtime__ref->days < days_to_epoch) || 
      (mtime__ref->days >= end_of_epoch) ||
      (mtime__ref->msecs < 0) ||
      (mtime__ref->msecs > secs_per_day*1000)) {
    *fres = get_error(Files__invalidTime, 0, NULL);
  } else {
    int res;
    int seconds = (mtime__ref->days - days_to_epoch) * secs_per_day +
                  (mtime__ref->msecs / 1000);
#if HAVE_UTIMES			/* we have microsecond resolution */
    struct timeval tpv[2];
    
    tpv[0].tv_sec = tpv[1].tv_sec = seconds;
    tpv[0].tv_usec = tpv[1].tv_usec = (mtime__ref->msecs % 1000) * 1000;
    res = utimes((char*)file__ref, tpv);
#else                           /* we only have second resolution */
    struct utimbuf times;
    
    times.actime = seconds;
    times.modtime = seconds;
    res = utime((const char*)file__ref, &times);
#endif

    if (res) {
      *fres = file_error((const char*)file__ref, NULL);
    } else {
      *fres = Files__done;
    }
  }
}

/* define the day count of the Unix epoch (Jan 1 1970 00:00:00 GMT) for the
   Time.TimeStamp format */
#define days_to_epoch 40587
#define secs_per_day 86400

void Files__GetModTime(const CHAR* file__ref, int file_0d, Time__TimeStamp *mtime, _Type mtime__tag, Files__Result *fres) {
  int res;
  struct stat stat_buf;

  res = stat((const char*)file__ref, &stat_buf);
  if (res == -1) {
    *fres = file_error((const char*)file__ref, NULL);
  } else {
    mtime->days = days_to_epoch + stat_buf.st_mtime / secs_per_day;
    mtime->msecs = (stat_buf.st_mtime % secs_per_day) * 1000;
#if HAVE_ST_MTIME_USEC
    mtime->msecs += (stat_buf.st_mtime_usec / 1000);
#endif
    *fres = Channel__done;
  }
}

extern BOOLEAN Files__Exists(const CHAR* file__ref, int file_0d) {
  return (access((const char*)file__ref, F_OK) == 0);
}

static void close_all_files (void) {
  while (open_files) {
    Files__FileDesc_Close (open_files);
  }
}

void Files_init(void) {
  int i;

  _mid = _register_module(&Files_md.md, &Files__WriterDesc_td.td);
  
  NEW_REC(Files__errorContext,Files__ErrorContextDesc);
  Msg__InitContext((Msg__Context)Files__errorContext, 
		   (const Msg__String)"OOC:Core:Files", 15);
  
  active_umask = umask (0);
  umask (active_umask);
  for(i=0; i<TMP_MIN; i++) {
    tmp_name[i] = NULL;
  }
  /* make sure that all files are closed upon program termination */
  Termination__RegisterProc (&close_all_files);
}
