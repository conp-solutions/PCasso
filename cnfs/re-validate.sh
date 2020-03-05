#!/bin/bash
#
# This script checks whether all CNF files in this directory can be solved
# without any issues (wrong answer, assertions, other faulty exit codes), except
# timeouts.
#
# If this script returns with exit code 0, alls CNFs are fine. Please note, as
# the tested solver might be parallel, a single successful run on a CNF might
# just not hit the issue.

# Fail in case something fails
set -e

script_dir=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

declare -i TIMEOUTS=0  # number of times we hit a timeout on a CNF
declare -i OVERALL_STATUS=0  # return code of this script

declare -a FAILURES=()

# Test all .cnf files there are
for f in $(find . -name "*.cnf")
do
	echo "Test $f" 1>&2

	STATUS=0
	"$script_dir"/toolCheck.sh "$script_dir"/pcasso.sh "$f" || STATUS="$?"
	echo "  finished with $STATUS" 1>&2

	if [ "$STATUS" -ne 0 ]
	then
		if [ "$STATUS" -eq 124 ]
		then
			TIMEOUTS=$((TIMEOUTS+1))
		else
			OVERALL_STATUS=1
			FAILURES+=("$f:$STATUS")
		fi
	fi
done

echo "Failures: ${FAILURES[*]}"

exit "$OVERALL_STATUS"
