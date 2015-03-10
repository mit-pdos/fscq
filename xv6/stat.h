#define T_DIR  1   // Directory
#define T_FILE 2   // File
#define T_DEV  3   // Device
#define T_SOCK 4   // Unix-domain socket

#ifdef FUSE
struct xv6stat {
#else
struct stat {
#endif
  short type;  // Type of file
  int dev;     // File system's disk device
  uint ino;    // Inode number
  short nlink; // Number of links to file
  uint size;   // Size of file in bytes
  int atime;
  int mtime;
  int ctime;
};
