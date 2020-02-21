for((i = 1;; ++i)); do
    echo $i
    ./gen $i > int
     ./a.out < int > out1
     ./correct2 < int > out2
     diff -w out1 out2 || break
   # diff -w <(./a < int) <(./brute < int) || break
done