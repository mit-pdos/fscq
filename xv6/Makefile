TARGETS = xv6fs mkfs

# Root for OSXFUSE includes and libraries
OSXFUSE_ROOT = /usr/local
#OSXFUSE_ROOT = /opt/local

INCLUDE_DIR = $(OSXFUSE_ROOT)/include/osxfuse/fuse
LIBRARY_DIR = $(OSXFUSE_ROOT)/lib

CC = gcc

CFLAGS_OSXFUSE = -I$(INCLUDE_DIR)
CFLAGS_OSXFUSE += -DFUSE_USE_VERSION=26
CFLAGS_OSXFUSE += -D_FILE_OFFSET_BITS=64
CFLAGS_OSXFUSE += -D_DARWIN_USE_64_BIT_INODE

CFLAGS_EXTRA = -DFUSEFS -Wall -g $(CFLAGS)

LIBS = -losxfuse


all: $(TARGETS)

OBJS = fuse.o log.o spinlock.o bio.o ide.o fs.o file.o pipe.o sysfile.o

xv6fs: $(OBJS)
	$(CC) $(CFLAGS_OSXFUSE)  -L$(LIBRARY_DIR) $(CFLAGS_EXTRA) -o $@ $^ $(LIBS)

-include $(OBJS:.o=.d)

%.o: %.c
	$(CC) -c -std=c99 $(CFLAGS_OSXFUSE) $(CFLAGS_EXTRA) $*.c -o $*.o

mkfs: mkfs.c fs.h
	gcc -Werror -Wall -o mkfs mkfs.c

FILES=hello.txt

fs.img: mkfs $(FILES)
	./mkfs fs.img $(FILES)

-include *.d

clean:
	rm -f $(TARGETS) *.o *.d
	rm -rf *.dSYM
