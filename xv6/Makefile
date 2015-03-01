TARGETS = xv6fs mkfs
CC = gcc
PKGFLAGS =`pkg-config fuse --cflags --libs`
CFLAGS_EXTRA = -DFUSEFS -MD -Wall -g $(PKGFLAGS)

all: $(TARGETS)

OBJS = fuse.o log.o spinlock.o bio.o ide.o fs.o file.o pipe.o sysfile.o

xv6fs: $(OBJS)
	$(CC) $^ $(CFLAGS_EXTRA) -o $@ 

-include $(OBJS:.o=.d)

%.o: %.c
	$(CC) -c $(CFLAGS_EXTRA) $*.c -o $*.o

mkfs: mkfs.c fs.h
	gcc -Werror -Wall -o mkfs mkfs.c

FILES=hello.txt

fs.img: mkfs $(FILES)
	./mkfs fs.img $(FILES)

-include *.d

clean:
	rm -f $(TARGETS) *.o *.d
