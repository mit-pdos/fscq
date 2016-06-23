#!/bin/sh

## Script to port code to new monadic prog. Every function no longer explicitly
## takes a continuation which it calls to constructor a prog, but instead directly
## constructs a prog, generally by calling Ret to explicitly return a value.

file="$1"

if [ -z "$file" ]; then
    echo "Usage: $0 <file>" >&2
    exit 1
fi

# Definition foo T args rx : prog T
#    becomes
# Definition foo args : prog _
#
# where the return type is now inferred, the same way that R is inferred in (rx
# : R -> prog T).
defsearch='Definition ([^ ]*) T (.*) (rx|\(rx ?:[^)]*\)) ?: prog T'
defrepl='Definition \1 \2 : prog _'
gsed -r -i "s/$defsearch/$defrepl/" "$file"

# Loops no longer require continuations, they just call Ret
gsed -r -i '/Continuation lrx/d' "$file"

# IfRx is no different from If now
gsed -r -i 's/IfRx irx/If/' "$file"

# Replace all continuations with Ret (rx for ordinary functions, lrx for loops,
# irx for IfRx). Note that Ret replaces the parameters removed by the above
# substitution.
gsed -r -i 's/\brx\b/Ret/g' "$file"
gsed -r -i 's/\blrx\b/Ret/g' "$file"
gsed -r -i 's/\birx\b/Ret/g' "$file"

# The generic composition progseq is now replaced by an explicit Bind
# constructor with a type specific to prog.
gsed -r -i 's/\bprogseq\b/Bind/g' "$file"

# Remaining lines with : prog T are untranslated programs, probably due to the
# continuation having an explicit type assertion. Print them as a warning.
grep -n ': prog T :=' "$file"

# return an error status if any untranslated programs were found, inverting the
# status of grep
if test "$?" -eq '0'; then
    exit 1
else
    exit 0
fi
