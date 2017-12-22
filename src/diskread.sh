#!/bin/sh

time -f '%es real  (%Us user, %Ks kernel)' taskset -c 0 diskread "$@" 2>&1
