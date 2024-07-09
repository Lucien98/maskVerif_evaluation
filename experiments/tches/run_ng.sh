
while read line;
do
	echo $line >> experiments/tches/results_ng.txt
	./maskverif < ${line} >> experiments/tches/results_ng.txt 2>&1
	echo "" >> experiments/tches/results_ng.txt
	echo "" >> experiments/tches/results_ng.txt
	echo "" >> experiments/tches/results_ng.txt
	echo "" >> experiments/tches/results_ng.txt

done < experiments/tches/benchs_ng.txt
