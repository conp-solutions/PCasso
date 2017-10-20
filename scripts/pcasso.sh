#!/bin/bash
# pcasso.sh, Norbert Manthey, 2014 - 2017
#
# solve CNF formula $1 by simplifying first with coprocessor, then run the pcasso SAT solver, and finally, reconstruct the model
# $2 points to the temporary directory (no trailing /)
#

# pcasso parameters (some out of many)
threads=12
child_nodes=7
# all parameters for pcasso
PCASSO_PARAM="-model -child-count=$child_nodes -threads=$threads"

# default parameters for preprocessor
cpParams="-enabled_cp3 -cp3_stats -bve -bve_red_lits=1 -fm -no-cp3_fm_vMulAMO -unhide -cp3_uhdIters=5 -cp3_uhdEE -cp3_uhdTrans -bce -bce-cle -no-bce-bce -dense"

#
# usage
#
if [ "x$1" = "x" ]; then
  echo "USAGE: pcasso.sh <input CNF> [<tmpDir> [arguments for cp3]]"
  exit 1
fi

# check whether all tools are present
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
if [ ! -x "$DIR/pcasso" ]
then
	echo "error: solver $DIR/pcasso could not be found, abort!"
	exit 1
fi
if [ ! -x "$DIR/coprocessor" ]
then
	echo "error: coprocessor $DIR/coprocessor could not be found, abort!"
	exit 1
fi
solver="$DIR/pcasso"
simplifier="$DIR/coprocessor"

#
# variables for the script
#
file=$1				# first argument is CNF instance to be solved
shift 1
tmpDir=$2			# directory to write the temporary files to
shift 1											# reduce the parameters, removed the very first one. remaining $@ parameters are arguments

# in case no tmpDir has been specified, create one and trap for deletion on exit
if [ -z "$tmpDir" ]
then
	tmpDir=$(mktemp -d)
	[ -z "$tmpDir" ] || trap "rm -rf $tmpDir" EXIT
fi



# some temporary files 
undo=$tmpDir/undo_$$						# path to temporary file that stores cp3 undo information
tmpCNF=$tmpDir/tmpCNF_$$				# path to temporary file that stores cp3 simplified formula
model=$tmpDir/model_$$					# path to temporary file that model of the preprocessor (stdout)
realModel=$tmpDir/realmodel_$$	# path to temporary file that model of the SAT solver (stdout)
echo "c undo: $undo tmpCNF: $tmpCNF model: $model realModel: $realModel"  1>&2

ppStart=0
ppEnd=0
solveStart=0
solveEnd=0

#
# run coprocessor with parameters added to this script
# and output to stdout of the preprocessor is redirected to stderr
#
ppStart=`date +%s`
$simplifier $file $realModel -enabled_cp3 -undo=$undo -dimacs=$tmpCNF $cpParams $@  1>&2
exitCode=$?
ppEnd=`date +%s`
echo "c preprocessed $(( $ppEnd - $ppStart)) seconds with exit code $exitCode" 1>&2
echo "c preprocessed $(( $ppEnd - $ppStart)) seconds with exit code $exitCode"

# solved by preprocessing
if [ "$exitCode" -eq "10" -o "$exitCode" -eq "20" ]
then 
	echo "c solved by preprocessor" 1>&2
else
	echo "c not solved by preprocessor -- do search" 1>&2
	if [ "$exitCode" -eq "0" ]
	then
		#
		# exit code == 0 -> could not solve the instance
		# dimacs file will be printed always
		# exit code could be 10 or 20, depending on whether coprocessor could solve the instance already
		#
	
		#
		# run your favorite solver (output is expected to look like in the SAT competition, s line and v line(s) )
		# and output to stdout of the sat solver is redirected to stderr
		#
		solveStart=`date +%s`
		$solver $tmpCNF $model $PCASSO_PARAM  1>&2
		exitCode=$?
		solveEnd=`date +%s`
		echo "c solved $(( $solveEnd - $solveStart )) seconds, exit code: $exitCode" 1>&2
		echo "c first solution line: `cat $model | head -n 1`"
	
		#
		# undo the model
		# coprocessor can also handle "s UNSATISFIABLE"
		#
		echo "c post-process with cp3" 1>&2
		$simplifier -post -undo=$undo -model=$model $cpParams > $realModel

	else
		#
		# preprocessor returned some unwanted exit code
		#
		echo "c preprocessor has been unable to solve the instance" 1>&2
		#
		# run sat solver on initial instance
		# and output to stdout of the sat solver is redirected to stderr
		#
		solveStart=`date +%s`
		$solver $file $realModel $PCASSO_PARAM 1>&2
		exitCode=$?
		solveEnd=`date +%s`
		echo "c solved $(( $solveEnd - $solveStart )) seconds" 1>&2
	fi
fi

#
# print times
#

echo "c pp-time: $(( $ppEnd - $ppStart)) solve-time: $(( $solveEnd - $solveStart ))" 1>&2

#
# print solution
#
cat $realModel;

#
# remove tmp files
#
rm -f $undo $undo.map $tmpCNF $model $realModel;

#
# return with correct exit code
#
echo "c exit with $exitCode"
exit $exitCode
