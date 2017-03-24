/*
 * largefile.c
 *
 * Implementation of the test described in Figure 9 of Rosenblum's LFS paper
 * ("The Design and Implementation of a Log-Structured File System", 13th
 * SOSP, 1991).
 *
 * "The figure shows the speed of a benchmark that creates a 100MB file with 
 * sequential writes, then reads the file back sequentially, then writes 
 * 100MB randomly to the existing file, then reads 100MB randomly from the
 * file, and finally reads the file sequentially again.  The bandwidth of
 * each of the of the five phases is shown separately."
 *
 * Unfortunately the description of the benchmark does not provide all of the
 * information required to reproduce.  It does not specify the size of
 * I/O operation used.  I allow this to be specified as a command line 
 * argument, so that we can play with different sizes easily.  They also
 * don't define the way the randomly read/write the file.  Do the 100MB of
 * random reads read each byte of the file once, or are they completely 
 * random?  My first implementation used the latter, this uses the former.
 *
 * Usage:
 *      largefile [-f file_size] [-i IO_size] [-s seed] dirname
 *
 * The test creates a test file in dirname.  file_size specifies the size
 * of the file in megabytes (defaults to 100).  IO_size specifies the size
 * of the IO transfers in kilobytes (defaults to 256).
 */

#define ONE_KB		(1024)			/* One Kilobyte */
#define ONE_MB		(1024*ONE_KB)		/* One Megabyte */

#define FILE_SIZE	(100*ONE_MB)		/* Default file size */
#define IO_SIZE		(256*ONE_KB)		/* Default I/O transfer size */
#define FILE_NAME	"LargeTestFile"		/* Name of test file */
#define NTEST		100000			/* Number of tests of */
						/*    gettimeofday() */
#define BLOCK_SIZE	8192

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/time.h>

#include "stats.h"

void usage();
int seq_read(), seq_write(), rand_read(), rand_write();

int timer_overhead;		/* Overhead of invoking timer */

int
main ( argc, argv )
int argc;
char *argv[];
{
    long fileSize;		/* Size of test file in bytes */
    int ioSize;			/* Size of I/O transfers in bytes */
    int seed;			/* Random number seed */
    int ch;			
    extern char *optarg;
    extern int optind;
    char *fileName;		/* Name of test file */
    struct timeval before;	/* Time stamps for measuring the overhead of */
    struct timeval after;	/*     the gettimeofday() call */
    struct timeval dummy;	/* Dummy for use in calibration */
    int usec;			/* Elapsed time for a test (in usec) */
    float sec;			/* Elapsed time for a test (in sec) */
    float throughput;		/* Throughput of a test, expressed in KB/sec */
    int fd;			/* File descriptor for test file */
    int i;

    /*
     * Parse and test the arguments.
     */
    fileSize = FILE_SIZE;
    ioSize = IO_SIZE;
    seed = getpid();
    while ( ( ch = getopt ( argc, argv, "f:i:s:" ) ) != EOF ) {
	switch ( ch ) {
	    case 'f':
		fileSize = atoi ( optarg ) * ONE_MB;
		break;
	    case 'i':
		ioSize = atoi ( optarg ) * ONE_KB;
		break;
	    case 's':
		seed = atoi ( optarg );
		break;
	    default:
		usage();
		exit(0);
	}
    }
    argc -= optind;
    argv += optind;

    if ( fileSize <= 0 ) {
	fprintf ( stderr, "Illegal file size!\n" );
	exit ( 1 );
    }
    if ( ioSize <= 0 ) {
	fprintf ( stderr, "Illegal I/O size\n" );
	exit ( 1 );
    }

    srandom ( seed );

    fileName = malloc ( strlen ( argv[0] ) + strlen ( FILE_NAME ) + 2 );
    if ( fileName == NULL ) {
	fprintf ( stderr, "Couldn't allocate memory for file name\n" );
	perror ( "malloc() failed" );
	exit ( 1 );
    }
    strcpy ( fileName, argv[0] );
    strcat ( fileName, "/" );
    strcat ( fileName, FILE_NAME );

    /*
     * Create the file
     */
    fd = open ( fileName, O_CREAT | O_TRUNC | O_RDWR, 0666 );
    if ( fd == -1 ) {
	fprintf ( stderr, "Couldn't create file %s\n", fileName );
	perror ( "open() failed" );
	exit ( 1 );
    }
    unlink ( fileName );

    /*
     * Compute the overhead of the gettimeofday() call.  
     */

    gettimeofday ( &before, NULL );
    for ( i = 0;  i < NTEST;  i++ ) 
	gettimeofday ( &dummy, NULL );
    gettimeofday ( &after, NULL );
    timer_overhead = (after.tv_sec - before.tv_sec) * 1000000 +
		     (after.tv_usec - before.tv_usec);
    timer_overhead /= NTEST;

    printstats(argv[0], 1);

    /*
     * Now we just do the tests in sequence, printing out the timing 
     * statistics as we go:
     */
    printf ( "\n\n\n" );
    fflush ( stdout );
    system ( "date" );
    printf ( "Running largefile test on %s\n", argv[0] );
    printf ( "File Size = %ld bytes\n", fileSize );
    printf ( "IO Size = %d bytes\n\n", ioSize );
    printf ( "Test		Time(sec)	KB/sec\n" );
    printf ( "----		---------	------\n" );

    usec = seq_write ( fd, fileSize, ioSize );
    sec = (float) usec / 1000000.0;
    throughput = ((float) fileSize / sec) / (float) ONE_KB;
    printf ( "seq_write\t%7.3f\t\t%7.3f\n", sec, throughput );
    fflush ( stdout );

    printstats(argv[0], 0);

    usec = seq_read ( fd, fileSize, ioSize );
    sec = (float) usec / 1000000.0;
    throughput = ((float) fileSize / sec) / (float) ONE_KB;
    printf ( "seq_read\t%7.3f\t\t%7.3f\n", sec, throughput );
    fflush ( stdout );

    usec = rand_write ( fd, fileSize, ioSize );
    sec = (float) usec / 1000000.0;
    throughput = ((float) fileSize / sec) / (float) ONE_KB;
    printf ( "rand_write\t%7.3f\t\t%7.3f\n", sec, throughput );
    fflush ( stdout );

    usec = rand_read ( fd, fileSize, ioSize );
    sec = (float) usec / 1000000.0;
    throughput = ((float) fileSize / sec) / (float) ONE_KB;
    printf ( "rand_read\t%7.3f\t\t%7.3f\n", sec, throughput );
    fflush ( stdout );

    usec = seq_read ( fd, fileSize, ioSize );
    sec = (float) usec / 1000000.0;
    throughput = ((float) fileSize / sec) / (float) ONE_KB;
    printf ( "re-read\t\t%7.3f\t\t%7.3f\n", sec, throughput );
    fflush ( stdout );

    close ( fd );
    exit ( 0 );
}

/*
 * seq_write()
 *
 * Sequentially write a file.  Both the size of the file and the size
 * of the writes are specified as parameters.  We return the number of
 * microseconds spent performing the I/O.  
 */
int
seq_write ( fd, fileSize, ioSize )
int fd;					/* File descriptor for I/O */
int fileSize;				/* Size of file */
int ioSize;				/* # of bytes per I/O operation */
{
    char *buffer;		/* I/O buffer */
    int ioCount;		/* Count of bytes transfered */
    int amt;			/* # of bytes for a specific write */
    int i;
    struct timeval before;	/* Time stamp before I/O operation */
    struct timeval after;	/* Time stamp after I/O operation */
    u_long time;		/* Cummulative elapsed time for writes */
    int rval;

    buffer = malloc ( ioSize );
    if ( buffer == NULL ) {
	fprintf ( stderr, "seq_write() couldn't allocate I/O buffer\n" );
	perror ( "malloc() failed" );
	exit ( 1 );
    }

    /*
     * Fill buffer, just in case OS does some weird optimization when
     * data is all zeros.
     */

    for ( i = 0;  i < ioSize;  i++ ) {
	buffer[i] = (char) i;
    }

    /*
     * Start from beginning of file.
     */
    rval = lseek ( fd, 0, SEEK_SET );
    if ( rval == -1 ) {
	fprintf ( stderr, "Couldn't seek to beginning of file\n" );
	perror ( "lseek() failed" );
	exit ( 1 );
    }

    /*
     * Do the writing.  We repeated call write() until the entire file
     * has been written.  We time each 
     */

    time = 0;
    ioCount = 0;
    gettimeofday ( &before, NULL );
    while ( ioCount < fileSize ) {
	if ( fileSize - ioCount >= ioSize ) {
	    amt = ioSize;
	} else {
	    amt = fileSize - ioCount;
	}

	rval = write ( fd, buffer, amt );

	if ( rval == -1 ) {
	    fprintf ( stderr, "Error in seq_write()\n" );
	    perror ( "write() failed" );
	    exit ( 1 );
	} else if ( rval != amt ) {
	    fprintf ( stderr, "Short write in seq_write().  %d bytes\n", rval );
	}
	ioCount += rval;
    }
    fsync ( fd );
    gettimeofday ( &after, NULL );
    time = time + (after.tv_sec - before.tv_sec) * 1000000 +
	(after.tv_usec - before.tv_usec);
    time -= timer_overhead;
    return ( time );
}

/*
 * seq_read()
 *
 * Sequentially read a file.  Both the size of the file and the size
 * of the reads are specified as parameters.  We return the number of
 * microseconds spent performing the I/O.  
 */
int
seq_read ( fd, fileSize, ioSize )
int fd;					/* File descriptor for I/O */
int fileSize;				/* Size of file */
int ioSize;				/* # of bytes per I/O operation */
{
    char *buffer;
    int ioCount;		/* Count of bytes transfered */
    int amt;			/* # of bytes for a specific read */
    struct timeval before;	/* Time stamp before I/O operation */
    struct timeval after;	/* Time stamp after I/O operation */
    u_long time;		/* Cummulative elapsed time for reads */
    int rval;

    buffer = malloc ( ioSize );
    if ( buffer == NULL ) {
	fprintf ( stderr, "seq_read() couldn't allocate I/O buffer\n" );
	perror ( "malloc() failed" );
	exit ( 1 );
    }

    /*
     * Start from beginning of file.
     */
    rval = lseek ( fd, 0, SEEK_SET );
    if ( rval == -1 ) {
	fprintf ( stderr, "Couldn't seek to beginning of file\n" );
	perror ( "lseek() failed" );
	exit ( 1 );
    }

    /*
     * Do the reading.  We repeated call read() until the entire file
     * has been read.  
     */

    time = 0;
    ioCount = 0;
    gettimeofday ( &before, NULL );
    while ( ioCount < fileSize ) {
	if ( fileSize - ioCount >= ioSize ) {
	    amt = ioSize;
	} else {
	    amt = fileSize - ioCount;
	}

	rval = read ( fd, buffer, amt );

	if ( rval == -1 ) {
	    fprintf ( stderr, "Error in seq_read()\n" );
	    perror ( "read() failed" );
	    exit ( 1 );
	} else if ( rval != amt ) {
	    fprintf ( stderr, "Short read in seq_read().  %d bytes\n", rval );
	}
	ioCount += rval;
    }
    gettimeofday ( &after, NULL );
    time = time + (after.tv_sec - before.tv_sec) * 1000000 +
	(after.tv_usec - before.tv_usec);
    time -= timer_overhead;
    return ( time );
}

/*
 * rand_write()
 *
 * Randomly write a file.  Both the size of the file and the size
 * of the writes are specified as parameters.  Each I/O operation is performed
 * from a random location in the file.  We return the number of
 * microseconds spent performing the I/O.  
 */
int
rand_write ( fd, fileSize, ioSize )
int fd;					/* File descriptor for I/O */
int fileSize;				/* Size of file */
int ioSize;				/* # of bytes per I/O operation */
{
    char *buffer;
    int ioCount;		/* Count of bytes transfered */
    int amt;			/* # of bytes for a specific write */
    int i,j;
    int nLocs;			/* Number of seek locations to use in file */
    char *seekArray;		/* Bitmap to keep track of which locations */
				/*     we've used. */
    int *seekOrder;		/* List of seek locations in order we will */
				/*     visit them. */
    struct timeval before;	/* Time stamp before I/O operation */
    struct timeval after;	/* Time stamp after I/O operation */
    u_long time;		/* Cummulative elapsed time for writes */
    int seekLocation;		/* Offset that we're going to seek to */
    int rval;

    buffer = malloc ( ioSize );
    if ( buffer == NULL ) {
	fprintf ( stderr, "rand_write() couldn't allocate I/O buffer\n" );
	perror ( "malloc() failed" );
	exit ( 1 );
    }

    /*
     * Fill buffer, just in case OS does some weird optimization when
     * data is all zeros.
     */

    for ( i = 0;  i < ioSize;  i++ ) {
	buffer[i] = (char) i;
    }

    /*
     * Determine seek order.  We divide the file up into ioSize pieces.  We
     * want to do one read/write of each piece.  To save time during the I/O,
     * we precomute the order in which we will use the pieces.  This is done
     * by starting with an array (seekArray) which has one element for each
     * piece of the file.  We randomly select an element from this array, and
     * mark it as used.  This will be the first part of the file that we will
     * read/write.  Then we randomly choose one of the unused elements of
     * seekArray as the second I/O location, etc.
     */
    nLocs = fileSize / ioSize;
    seekArray = calloc ( nLocs, sizeof ( char ) );
    seekOrder = malloc ( nLocs * sizeof ( int ) );
    for ( i = nLocs;  i > 0;  i-- ) {
	seekLocation = random() % i;
	for ( j = 0;  seekArray[j] == 1  ||  seekLocation > 0 ; j++ ) {
	    if ( seekArray[j] == 0 ) {
		seekLocation--;
	    }
	}
	seekArray[j] = 1;
	seekOrder[nLocs - i] = j;
    }

    /*
     * Do the writing.  We repeated call write() until the entire file
     * has been written.  
     */

    time = 0;
    ioCount = 0;
    seekLocation = 0;
    gettimeofday ( &before, NULL );

    for (int iter = 0; iter < 64; iter++) {

    ioCount = 0;
    seekLocation = 0;

    while ( ioCount < fileSize ) {

	/*
	 * Go to a random point in the file. 
	 */
	rval = lseek ( fd, seekOrder[seekLocation]*ioSize, SEEK_SET );
	seekLocation++;
	if ( rval == -1 ) {
	    fprintf ( stderr, "Error in rand_write()\n" );
	    perror ( "lseek() failed" );
	    exit ( 1 );
	}

	if ( fileSize - ioCount >= ioSize ) {
	    amt = ioSize;
	} else {
	    amt = fileSize - ioCount;
	}

	rval = write ( fd, buffer, amt );
	if ( rval == -1 ) {
	    fprintf ( stderr, "Error in rand_write()\n" );
	    perror ( "write() failed" );
	    exit ( 1 );
	} else if ( rval != amt ) {
	    fprintf ( stderr, "Short write in rand_write().  %d bytes\n", rval );
	}
	ioCount += rval;

        fdatasync(fd);
    }

    }

    fsync ( fd );
    gettimeofday ( &after, NULL );
    time = time + (after.tv_sec - before.tv_sec) * 1000000 +
        (after.tv_usec - before.tv_usec);
    time -= timer_overhead;
    return ( time );
}

/*
 * rand_read()
 *
 * Randomly read a file.  Both the size of the file and the size
 * of the reads are specified as parameters.  Each read starts at a random
 * location in the file.  We return the number of microseconds spent
 * performing the I/O.  
 */
int
rand_read ( fd, fileSize, ioSize )
int fd;					/* File descriptor for I/O */
int fileSize;				/* Size of file */
int ioSize;				/* # of bytes per I/O operation */
{
    char *buffer;
    int ioCount;		/* Count of bytes transfered */
    int amt;			/* # of bytes for a specific read */
    int i,j;
    int nLocs;			/* Number of seek locations to use in file */
    char *seekArray;		/* Bitmap to keep track of which locations */
				/*     we've used. */
    int *seekOrder;		/* List of seek locations in order we will */
				/*     visit them. */
    struct timeval before;	/* Time stamp before I/O operation */
    struct timeval after;	/* Time stamp after I/O operation */
    u_long time;		/* Cummulative elapsed time for reads */
    int rval;
    int seekLocation;

    buffer = malloc ( ioSize );
    if ( buffer == NULL ) {
	fprintf ( stderr, "rand_read() couldn't allocate I/O buffer\n" );
	perror ( "malloc() failed" );
	exit ( 1 );
    }

    /*
     * Determine seek order.  We divide the file up into ioSize pieces.  We
     * want to do one read/write of each piece.  To save time during the I/O,
     * we precomute the order in which we will use the pieces.  This is done
     * by starting with an array (seekArray) which has one element for each
     * piece of the file.  We randomly select an element from this array, and
     * mark it as used.  This will be the first part of the file that we will
     * read/write.  Then we randomly choose one of the unused elements of
     * seekArray as the second I/O location, etc.
     */
    nLocs = fileSize / ioSize;
    seekArray = calloc ( nLocs, sizeof ( char ) );
    seekOrder = malloc ( nLocs * sizeof ( int ) );
    for ( i = nLocs;  i > 0;  i-- ) {
	seekLocation = random() % i;
	for ( j = 0;  seekArray[j] == 1  ||  seekLocation > 0 ; j++ ) {
	    if ( seekArray[j] == 0 ) {
		seekLocation--;
	    }
	}
	seekArray[j] = 1;
	seekOrder[nLocs - i] = j;
    }

    /*
     * Do the reading.  We repeated call read() until the entire file
     * has been read.  
     */

    time = 0;
    ioCount = 0;
    seekLocation = 0;
    gettimeofday ( &before, NULL );
    while ( ioCount < fileSize ) {
	if ( fileSize - ioCount >= ioSize ) {
	    amt = ioSize;
	} else {
	    amt = fileSize - ioCount;
	}

	/*
	 * Go to a random point in the file.  
	 */
	rval = lseek ( fd, seekOrder[seekLocation]*ioSize, SEEK_SET );
	seekLocation++;
	if ( rval == -1 ) {
	    fprintf ( stderr, "Error in rand_read()\n" );
	    perror ( "lseek() failed" );
	    exit ( 1 );
	}

	/*
	 * Do the read operation
	 */
	rval = read ( fd, buffer, amt );

	if ( rval == -1 ) {
	    fprintf ( stderr, "Error in seq_read()\n" );
	    perror ( "read() failed" );
	    exit ( 1 );
	} else if ( rval != amt ) {
	    fprintf ( stderr, "Short read in seq_read().  %d bytes\n", rval );
	}
	ioCount += rval;
    }
    gettimeofday ( &after, NULL );
    time = time + (after.tv_sec - before.tv_sec) * 1000000 +
	(after.tv_usec - before.tv_usec);
    time -= timer_overhead;
    return ( time );
}

void 
usage()
{
    fprintf ( stderr, "Usage:  largefile [-f file_size] [-i IO_size] test_directory\n" );
}
