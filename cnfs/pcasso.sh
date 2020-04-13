# gdb -return-child-result -x gdb-script --args \
	./pcasso -model -child-count=7 -threads=3 \
	-no-lbd-min \
	$1
