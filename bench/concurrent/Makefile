all: fsops timeres large_small parallel_ls

%: %.c timing.h
	gcc -Wall -Werror -O2 -pthread $< -o $@
