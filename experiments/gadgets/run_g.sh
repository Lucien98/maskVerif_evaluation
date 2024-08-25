
while read line;
do
	echo $line >> experiments/gadgets/results_g.txt
	./maskverif < ${line} >> experiments/gadgets/results_g.txt 2>&1
	echo "" >> experiments/gadgets/results_g.txt
	echo "" >> experiments/gadgets/results_g.txt
	echo "" >> experiments/gadgets/results_g.txt
	echo "" >> experiments/gadgets/results_g.txt

done < experiments/gadgets/benchs_g.txt
