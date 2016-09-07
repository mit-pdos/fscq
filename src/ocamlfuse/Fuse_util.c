/*
  This file is part of the "OCamlFuse" library.

  OCamlFuse is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation (version 2 of the License).
  
  OCamlFuse is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with OCamlFuse.  See the file LICENSE.  If you haven't received
  a copy of the GNU General Public License, write to:
  
  Free Software Foundation, Inc.,
  59 Temple Place, Suite 330, Boston, MA
  02111-1307  USA

  Vincenzo Ciancia

  applejack@users.sf.net
  vincenzo_ml@yahoo.it
*/

#define UNKNOWN_ERR 127

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/bigarray.h>
#include <caml/camlidlruntime.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <math.h>
#include <sys/types.h>
#include <dirent.h>
#include <sys/stat.h>
#include <fcntl.h>

#define FUSE_USE_VERSION 26
#include <fuse.h>
#include <sys/types.h>
#include <sys/xattr.h>

#include "Fuse_bindings.h"

#define min(a,b) (a<b?a:b)

//TODO: below no CAMLprim, CAMLparam, CAMLlocal, is this ok?
value callback4(value closure,value arg1,value arg2,value arg3,value arg4)
{
  value args[4]={arg1,arg2,arg3,arg4};
  return callbackN(closure,4,args);
}

CAMLprim value c2ml_setxattr_flags(int flags)
{
  CAMLparam0 ();
  CAMLlocal1(res);

  if (flags==XATTR_CREATE)
    {
      res=Val_int(1);
    }
  else if (flags==XATTR_REPLACE)
    {
      res=Val_int(2);
    }
  else res=Val_int(0);

  CAMLreturn(res);
}

/* This part shamelessly copied from mlfuse */
#define ADDFLAGT(T, X) \
  num_ml_constr--;\
  if (T) {\
    tmp = alloc_small (2, 0);\
    Field (tmp, 0) = Val_int (num_ml_constr);\
    Field (tmp, 1) = res;\
    res = tmp;\
  }

#define ADDFLAG(X) ADDFLAGT(flags & X, X)
#define ADDBASEFLAG(X) ADDFLAGT((flags & 3) == X, X)

CAMLprim value c_flags_to_open_flag_list (int flags) {
  CAMLparam0 ();
  CAMLlocal2 (res, tmp);
  int num_ml_constr = 8;

  res = Val_int (0);

  ADDFLAG (O_EXCL);
  ADDFLAG (O_TRUNC);
  ADDFLAG (O_CREAT);
  ADDFLAG (O_APPEND);
  ADDFLAG (O_NONBLOCK);

  ADDBASEFLAG (O_RDWR);
  ADDBASEFLAG (O_WRONLY);
  ADDBASEFLAG (O_RDONLY);

  CAMLreturn (res);
}
/* End of shame */

static int ml2c_unix_error_vect[] = 
{ 
  E2BIG,
  EACCES,
  EAGAIN,
  EBADF,
  EBUSY,
  ECHILD,
  EDEADLK,
  EDOM ,
  EEXIST,
  EFAULT,
  EFBIG,
  EINTR,
  EINVAL,
  EIO,
  EISDIR,
  EMFILE,
  EMLINK,
  ENAMETOOLONG,
  ENFILE,
  ENODEV,
  ENOENT,
  ENOEXEC,
  ENOLCK,
  ENOMEM,
  ENOSPC,
  ENOSYS,
  ENOTDIR,
  ENOTEMPTY,
  ENOTTY,
  ENXIO,
  EPERM,
  EPIPE,
  ERANGE,
  EROFS,
  ESPIPE,
  ESRCH,
  EXDEV,
  EWOULDBLOCK,
  EINPROGRESS,
  EALREADY,
  ENOTSOCK,
  EDESTADDRREQ,
  EMSGSIZE,
  EPROTOTYPE,
  ENOPROTOOPT,
  EPROTONOSUPPORT ,
  ESOCKTNOSUPPORT ,
  EOPNOTSUPP,
  EPFNOSUPPORT,
  EAFNOSUPPORT,
  EADDRINUSE,
  EADDRNOTAVAIL,
  ENETDOWN,
  ENETUNREACH,
  ENETRESET,
  ECONNABORTED,
  ECONNRESET,
  ENOBUFS,
  EISCONN,
  ENOTCONN,
  ESHUTDOWN,
  ETOOMANYREFS,
  ETIMEDOUT,
  ECONNREFUSED,
  EHOSTDOWN,
  EHOSTUNREACH,
  ELOOP,
  EOVERFLOW,
  0 /* Terminator for the inverse function */
};

static int ml2c_unix_error_vect_dim=0;

int ml2c_unix_error(int ocaml_err)
{
  if (ocaml_err < ml2c_unix_error_vect_dim)
    return ml2c_unix_error_vect[ocaml_err];
  return UNKNOWN_ERR; /* TODO: find an appropriate value */
}

/* TODO: This sucks */

int * invert_array(int * src,int * indim,int * outdim)
{
  /* Find dimensions */
  int dim=0;
  int i=0;
  int srcdim = 0;

  while (src[srcdim]!=0) 
    {
      if (src[srcdim]>dim) dim=src[srcdim]; 
      srcdim++;
    }
  
  /* Create the result */
  int * res = malloc(dim * sizeof(int));
  for (i = 0;i < dim;i++) res[i]=UNKNOWN_ERR; /* TODO: find a meaningful value */
  
  /* Invert the array */
  for (i = 0;i < srcdim;i++) res[src[i]]=i;

  *indim=srcdim;
  *outdim=dim;
  return res;
}

static int c2ml_unix_error_vect_dim=0;
static int * c2ml_unix_error_vect;

int c2ml_unix_error(int c_err)
{
  if (c_err < c2ml_unix_error_vect_dim)
    return c2ml_unix_error_vect[c_err];
  return UNKNOWN_ERR; /* TODO: find a meaningful value (also search for UNKNOWN_ERR in this file */
}

/* end "Thisk sucks" part */

int c2ml_mode_t_kind(mode_t m)
{
  if (S_ISREG(m))
    return Val_int(0);
  else if (S_ISDIR(m))
    return Val_int(1);
  else if (S_ISCHR(m))
    return Val_int(2);
  else if (S_ISBLK(m))
    return Val_int(3);
  else if (S_ISLNK(m))
    return Val_int(4);
  else if (S_ISFIFO(m))
    return Val_int(5);
  else if (S_ISSOCK(m))
    return Val_int(6);

  // Unknown type; pretend like it's S_REG..
  return Val_int(0);
}

int c2ml_mode_t_perm(mode_t m)
{
  return Val_int(m & ~S_IFMT);
}

int ml2c_unix_file_kind[] =
{
  S_IFREG,
  S_IFDIR,
  S_IFCHR,
  S_IFBLK,
  S_IFLNK,
  S_IFIFO,
  S_IFSOCK
};

void ml2c_Unix_stats_struct_stat(value v,struct stat * s)
{
  memset(s,0,sizeof(*s));
  s->st_dev=Int_val(Field(v,0));
  s->st_ino=Int_val(Field(v,1));
  s->st_mode=0 | Int_val(Field(v,3)) | ml2c_unix_file_kind[Int_val(Field(v,2))];
  s->st_nlink=Int_val(Field(v,4));
  s->st_uid=Int_val(Field(v,5));
  s->st_gid=Int_val(Field(v,6));
  s->st_rdev=Int_val(Field(v,7));
  s->st_size=Int64_val(Field(v,8)); 
  s->st_blksize=512; /* TODO: STUB, at least use the one from statfs */
  s->st_blocks=ceil(((double)s->st_size)/((double)s->st_blksize)); /* TODO: STUB! */
  s->st_atime=Double_val(Field(v,9));
  s->st_mtime=Double_val(Field(v,10));
  s->st_ctime=Double_val(Field(v,11));
}

void ml2c_Unix_struct_statvfs(value v,struct statvfs * st)
{
  memset(st,0,sizeof(*st));
  st->f_bsize = Int64_val(Field(v,0));
  st->f_frsize = Int64_val(Field(v,1));
  st->f_blocks = Int64_val(Field(v,2));
  st->f_bfree = Int64_val(Field(v,3));
  st->f_bavail = Int64_val(Field(v,4));
  st->f_files = Int64_val(Field(v,5));
  st->f_ffree = Int64_val(Field(v,6));
  st->f_favail = Int64_val(Field(v,7));
  st->f_fsid = Int64_val(Field(v,8));
  st->f_flag = Int64_val(Field(v,9));
  st->f_namemax = Int64_val(Field(v,10));

  /* TODO: check the meaning of the following missing field:
     __f_spare
   */
}

#define FOR_ALL_OPS(MACRO) \
    MACRO(init) \
    MACRO(getattr) \
    MACRO(readlink) \
    MACRO(readdir) \
    MACRO(opendir) \
    MACRO(releasedir) \
    MACRO(fsyncdir) \
    MACRO(mknod) \
    MACRO(mkdir) \
    MACRO(symlink) \
    MACRO(unlink) \
    MACRO(rmdir) \
    MACRO(rename) \
    MACRO(link) \
    MACRO(chmod) \
    MACRO(chown) \
    MACRO(truncate) \
    MACRO(utime) \
    MACRO(open) \
    MACRO(read) \
    MACRO(write) \
    MACRO(statfs) \
    MACRO(release) \
    MACRO(flush) \
    MACRO(fsync) \
    MACRO(setxattr) \
    MACRO(getxattr) \
    MACRO(listxattr) \
    MACRO(removexattr)

/* 
   TODO: missing callbacks for fuse API version 2.7

   CALLS INTRODUCED FROM 2.3 ON

   unsigned int 	flag_nullpath_ok: 1
   void(* 	destroy )(void *)
   int(* 	access )(const char *, int)
   int(* 	create )(const char *, mode_t, struct fuse_file_info *)
   int(* 	ftruncate )(const char *, off_t, struct fuse_file_info *)
   int(* 	fgetattr )(const char *, struct stat *, struct fuse_file_info *)
   int(* 	lock )(const char *, struct fuse_file_info *, int cmd, struct flock *)
   int(* 	utimens )(const char *, const struct timespec tv[2])
   int(* 	bmap )(const char *, size_t blocksize, uint64_t *idx)
   int(* 	ioctl )(const char *, int cmd, void *arg, struct fuse_file_info *, unsigned int flags, void *data)
   int(* 	poll )(const char *, struct fuse_file_info *, struct fuse_pollhandle *ph, unsigned *reventsp)
*/

#define SET_NULL_OP(OPNAME) .OPNAME = NULL,

static struct fuse_operations ops = {
  FOR_ALL_OPS(SET_NULL_OP)
};

static value * ocaml_list_length=NULL;

#define DECLARE_OP_CLOSURE(OPNAME) static value * OPNAME##_closure=NULL;
FOR_ALL_OPS(DECLARE_OP_CLOSURE)

#define init_ARGS (struct fuse_conn_info *conn)
#define init_RTYPE void *
#define init_CB vres=callback(*init_closure,Val_unit);
/* TODO: the result from init is wrong, it should return unit */
#define init_RES 

#define getattr_ARGS (const char* path, struct stat * buf)
#define getattr_RTYPE int
#define getattr_CB vpath = copy_string(path); vres=callback(*getattr_closure,vpath);
#define getattr_RES \
  ml2c_Unix_stats_struct_stat(Field(vres,0),buf);

/* TODO: allow ocaml to use the offset and the stat argument of the filler */
#define readdir_ARGS (const char * path, void * buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info * info)
#define readdir_RTYPE int
#define readdir_CB vpath = copy_string(path); vres=callback2(*readdir_closure,vpath,Val_int(info->fh));
#define readdir_RES \
  vtmp=Field(vres,0);	    \
  while (Is_block(vtmp))    \
    { \
      if (filler(buf,String_val(Field(vtmp,0)),NULL,0)) break; \
      if (res != 0) break;				    \
      vtmp=Field(vtmp,1);				    \
    }

#define mknod_ARGS (const char *path, mode_t mode, dev_t rdev)
#define mknod_RTYPE int
#define mknod_CB vpath = copy_string(path); vres=callback4(*mknod_closure,vpath,c2ml_mode_t_kind(mode),c2ml_mode_t_perm(mode),Val_int(rdev));
#define mknod_RES

#define mkdir_ARGS (const char *path, mode_t mode)
#define mkdir_RTYPE int
#define mkdir_CB vpath = copy_string(path); vres=callback2(*mkdir_closure,vpath,Val_int(mode));
#define mkdir_RES

#define unlink_ARGS (const char *path)
#define unlink_RTYPE int
#define unlink_CB vpath = copy_string(path); vres=callback(*unlink_closure,vpath);
#define unlink_RES

#define rmdir_ARGS (const char *path)
#define rmdir_RTYPE int
#define rmdir_CB vpath = copy_string(path); vres=callback(*rmdir_closure,vpath);
#define rmdir_RES

#define readlink_ARGS (const char *path, char *buf, size_t size)
#define readlink_RTYPE int
#define readlink_CB vpath = copy_string(path); vres=callback(*readlink_closure,vpath);
#define readlink_RES strncpy(buf,String_val(Field(vres,0)),size-1);

#define symlink_ARGS (const char *path, const char *dest)
#define symlink_RTYPE int
#define symlink_CB \
     vpath = copy_string(path); \
     vtmp = copy_string(dest); \
     vres=callback2(*symlink_closure,vpath,vtmp);
#define symlink_RES

#define rename_ARGS (const char *path, const char *dest)
#define rename_RTYPE int
#define rename_CB \
     vpath = copy_string(path); \
     vtmp = copy_string(dest); \
     vres=callback2(*rename_closure,vpath,vtmp);
#define rename_RES

#define link_ARGS (const char *path, const char *dest)
#define link_RTYPE int
#define link_CB  \
     vpath = copy_string(path); \
     vtmp = copy_string(dest); \
     vres=callback2(*link_closure,vpath,vtmp);
#define link_RES

#define chmod_ARGS (const char *path, mode_t mode)
#define chmod_RTYPE int
#define chmod_CB vpath = copy_string(path); vres=callback2(*chmod_closure,vpath,Val_int(mode));
#define chmod_RES

#define chown_ARGS (const char *path, uid_t uid, gid_t gid)
#define chown_RTYPE int
#define chown_CB vpath = copy_string(path); vres=callback3(*chown_closure,vpath,Val_int(uid),Val_int(gid));
#define chown_RES

#define truncate_ARGS (const char *path, off_t size)
#define truncate_RTYPE int
#define truncate_CB vpath = copy_string(path); vres=callback2(*truncate_closure,vpath,copy_int64(size));
#define truncate_RES

#define utime_ARGS (const char *path, struct utimbuf *buf)
#define utime_RTYPE int
#define utime_CB vpath = copy_string(path); vres=callback3(*utime_closure,vpath,copy_double(buf->actime),copy_double(buf->modtime));
#define utime_RES

#define open_ARGS (const char *path, struct fuse_file_info *fi)
#define open_RTYPE int
#define open_CB vpath = copy_string(path); vres=callback2(*open_closure,vpath,c_flags_to_open_flag_list(fi->flags));
#define open_RES if (Field(vres,0) != Val_int(0)) fi->fh = Int_val(Field(Field(vres,0),0));

#define opendir_ARGS (const char *path, struct fuse_file_info *fi)
#define opendir_RTYPE int
#define opendir_CB vpath = copy_string(path); vres=callback2(*opendir_closure,vpath,c_flags_to_open_flag_list(fi->flags));
#define opendir_RES if (Field(vres,0) != Val_int(0)) fi->fh = Int_val(Field(Field(vres,0),0));

#define read_ARGS (const char *path, char *buf, size_t size, off_t offset,struct fuse_file_info * fi)
#define read_RTYPE int
#define read_CB \
  vpath = copy_string(path); \
  vres=callback4(*read_closure,vpath,alloc_bigarray_dims(BIGARRAY_UINT8|BIGARRAY_C_LAYOUT,1,buf,size),copy_int64(offset),Val_int(fi->fh));
#define read_RES res=Int_val(Field(vres,0));

#define write_ARGS (const char *path, const char *buf, size_t size,off_t offset,struct fuse_file_info * fi) /* TODO: check usage of the writepages field of fi */
#define write_RTYPE int
#define write_CB \
  vpath = copy_string(path); \
  vres=callback4(*write_closure,vpath,alloc_bigarray_dims(BIGARRAY_UINT8|BIGARRAY_C_LAYOUT,1,(char *)buf,size),copy_int64(offset),Val_int(fi->fh)); 
#define write_RES res=Int_val(Field(vres,0));

#define release_ARGS (const char *path, struct fuse_file_info * fi) 
#define release_RTYPE int
#define release_CB vpath = copy_string(path); vres=callback3(*release_closure,vpath,c_flags_to_open_flag_list(fi->flags),Val_int(fi->fh));
#define release_RES

#define releasedir_ARGS (const char *path, struct fuse_file_info * fi) 
#define releasedir_RTYPE int
#define releasedir_CB vpath = copy_string(path); vres=callback3(*releasedir_closure,vpath,c_flags_to_open_flag_list(fi->flags),Val_int(fi->fh));
#define releasedir_RES

#define flush_ARGS (const char *path,struct fuse_file_info * fi)
#define flush_RTYPE int
#define flush_CB vpath = copy_string(path); vres=callback2(*flush_closure,vpath,Val_int(fi->fh));
#define flush_RES 

#define statfs_ARGS (const char *path, struct statvfs *stbuf)
#define statfs_RTYPE int
#define statfs_CB vpath = copy_string(path); vres=callback(*statfs_closure,vpath);
#define statfs_RES ml2c_Unix_struct_statvfs(Field(vres,0),stbuf);

#define fsync_ARGS (const char *path, int isdatasync,struct fuse_file_info * fi) 
#define fsync_RTYPE int
#define fsync_CB vpath = copy_string(path); vres=callback3(*fsync_closure,vpath,Val_bool(isdatasync),Val_int(fi->fh));
#define fsync_RES

#define fsyncdir_ARGS (const char *path, int isdatasync,struct fuse_file_info * fi) 
#define fsyncdir_RTYPE int
#define fsyncdir_CB vpath = copy_string(path); vres=callback3(*fsync_closure,vpath,Val_bool(isdatasync),Val_int(fi->fh));
#define fsyncdir_RES

#define setxattr_ARGS (const char *path, const char *name, const char *val,size_t size,int flags)
#define setxattr_RTYPE int
#define setxattr_CB \
    vpath = copy_string(path); \
    vstring = alloc_string(size); \
    memcpy(String_val(vstring),val,size); \
    vres=callback4(*setxattr_closure,vpath,copy_string(name),vstring,c2ml_setxattr_flags(flags));
#define setxattr_RES

#define getxattr_ARGS (const char *path, const char *name, char *val,size_t size)
#define getxattr_RTYPE int
#define getxattr_CB \
  vpath = copy_string(path); \
  vres=callback2(*getxattr_closure,vpath,copy_string(name));
#define getxattr_RES \
     res=string_length(Field(vres,0)); \
     if (size > 0) \
        if (string_length(Field(vres,0))>=size) \
        { \
           res = -UNKNOWN_ERR; \
        } \
        else \
        { \
	  memcpy(val,String_val(Field(vres,0)),string_length(Field(vres,0))); \
        }

#define listxattr_ARGS (const char *path, char *list, size_t size)
#define listxattr_RTYPE int
#define listxattr_CB vpath = copy_string(path); vres=callback(*listxattr_closure,vpath);
#define listxattr_RES \
     vtmp=Field(Field(vres,0),0);\
     int len; \
     char * dest=list; \
     int rem=size; \
     if (size==0) \
     { \
        res = Int_val(Field(Field(vres,0),1)); \
     } \
     else \
     { \
        while (Is_block(vtmp)) \
        { \
           len = string_length(Field(vtmp,0))+1; \
           if (rem>=len) \
           { \
              memcpy(dest,String_val(Field(vtmp,0)),len); \
              vtmp=Field(vtmp,1);\
              dest+=len; \
              rem=rem-len; \
           } \
           else \
           { \
             res = -ERANGE; \
             break; \
           } \
        } \
        res=size-rem; \
     }

#define removexattr_ARGS (const char *path, const char *name)
#define removexattr_RTYPE int
#define removexattr_CB vpath = copy_string(path); vres=callback2(*removexattr_closure,vpath,copy_string(name));
#define removexattr_RES

#define CALLBACK(OPNAME) \
static OPNAME##_RTYPE ops_##OPNAME OPNAME##_ARGS \
{ \
  leave_blocking_section(); \
  value vstring; \
  value vpath; \
  value vres; \
  value vtmp; \
  int res=-1; \
  OPNAME##_CB \
  if (Tag_val(vres)==1) /* Result is not Bad */ \
     { \
       res=0; \
       OPNAME##_RES /* res can be changed here */ \
     } \
  else \
  { \
    if (Is_block(Field(vres,0)))  /* This is EUNKNOWNERR of int in ocaml */ \
	res=-Int_val(Field(Field(vres,0),0));				\
    else res=-ml2c_unix_error(Int_val(Field(vres,0))); \
  } \
  enter_blocking_section(); \
  return res; \
}

FOR_ALL_OPS(CALLBACK)

#define SET_OPERATION(OPNAME) \
  if (op->OPNAME==NULL) ops.OPNAME=NULL; \
  else \
    { \
      OPNAME##_closure=caml_named_value(op->OPNAME); \
      ops.OPNAME=ops_##OPNAME; \
    }

void set_fuse_operations(struct fuse_operation_names const *op) 
{
  FOR_ALL_OPS(SET_OPERATION)
}

struct fuse_operations * get_fuse_operations()
{
  return &ops;
}

value * ocaml_fuse_loop_closure;

int mainloop(struct fuse * f,int multithreaded)
{
  if (f == NULL)
    return(-1);
  
  value _fuse=alloc_small(1, Abstract_tag);
  Field(_fuse, 0) = (value) f;
  
  return callback2(*ocaml_fuse_loop_closure,_fuse,Val_bool(multithreaded));
}

void ml_fuse_init()
{
  c2ml_unix_error_vect = invert_array(ml2c_unix_error_vect,&ml2c_unix_error_vect_dim,&c2ml_unix_error_vect_dim); /* TODO: this sucks together with the one at the beginning of file */
}

void ml_fuse_main(int argc,str * argv,struct fuse_operations const * op)
{
  ocaml_fuse_loop_closure = caml_named_value("ocaml_fuse_loop");
  ocaml_list_length = caml_named_value("ocaml_list_length");

  char * mountpoint;
  int multithreaded;
  int fd;

  struct fuse * fuse = fuse_setup(argc,argv,op,sizeof(struct fuse_operations),&mountpoint,&multithreaded,&fd);

  if (fuse!=NULL) 
    {
      mainloop(fuse,multithreaded);
      fuse_teardown(fuse,mountpoint);
    }
}

value ocaml_fuse_is_null(value v) /* For Com.opaque values */
{
  return Val_bool(0==Field(v,0)); // Is this the right way to check for null?
}

