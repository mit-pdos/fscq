#ifdef FUSE
#define XV6_O_RDONLY  0x000
#define XV6_O_WRONLY  0x001
#define XV6_O_RDWR    0x002
#define XV6_O_CREATE  0x200
#else
#define O_RDONLY  0x000
#define O_WRONLY  0x001
#define O_RDWR    0x002
#define O_CREATE  0x200
#endif
