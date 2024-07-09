
while read line;
do
	echo $line >> experiments/tches/results_g.txt
	./maskverif < ${line} >> experiments/tches/results_g.txt 2>&1
	echo "" >> experiments/tches/results_g.txt
	echo "" >> experiments/tches/results_g.txt
	echo "" >> experiments/tches/results_g.txt
	echo "" >> experiments/tches/results_g.txt

done < experiments/tches/benchs_g.txt
