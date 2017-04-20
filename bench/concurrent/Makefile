all: fsops timeres large_small parallel_ls

%: %.c
	gcc -Wall -Werror -O2 -pthread $< -o $@
