all: fsops timeres large_small

%: %.c
	gcc -Wall -Werror -O2 -pthread $< -o $@
