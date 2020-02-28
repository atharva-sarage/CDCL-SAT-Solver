#!/bin/bash
mkdir dump
#UUF175.753.100
#CBS_k3_n100_m403_b10
#UUF200.860.1000

g++ -o a2.out solver2.cpp --std=c++11 -O3
rm ./dump/out1.txt
for filename in $1/*.cnf; do   
    echo "$filename"
    ./a2.out < $filename >> ./dump/out1.txt
    #./correct2 < $filename >> correctAns3.txt
    time ./a.out < $filename
    echo "$filename"
done
#diff -w correctAns3.txt ./dump/out100.txt
diff -w correctAns.txt ./dump/out1.txt