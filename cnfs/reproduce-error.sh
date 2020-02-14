#!/bin/bash
FILE="$1"

I=0
S=10

# run until we hit wrong unsat, or an assertion
while [ $S -ne 25 ] && [ $S -ne 134 ] 
do
	echo $I
	I=$((I+1))
	rm -f /tmp/pcasso-*.log
	./toolCheck.sh ./pcasso.sh "$FILE" &> last.log 
	S=$?
	echo $S
        # stop after 200 iterations
	[ "$I" -lt 200 ] || break
done

echo "check output in file last.log!"
