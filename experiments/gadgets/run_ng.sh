
while read line;
do
	echo $line >> experiments/gadgets/results_ng.txt
	./maskverif < ${line} >> experiments/gadgets/results_ng.txt 2>&1
	echo "" >> experiments/gadgets/results_ng.txt
	echo "" >> experiments/gadgets/results_ng.txt
	echo "" >> experiments/gadgets/results_ng.txt
	echo "" >> experiments/gadgets/results_ng.txt

done < experiments/gadgets/benchs_ng.txt
