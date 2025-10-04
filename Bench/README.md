To Generate data
run 
```bash
lake build datagen -R
```
then 

```bash
time ./.lake/build/bin/datagen --unique-ratio=0.1,0.25,0.5,0.75,0.9,1 --swaps-ratio=0,0.001,0.01,0.05,0.1,0.5 --reverse --forward 1000 10000 100000 1000000

time ./.lake/build/bin/datagen --unique-ratio=0,0.1,0.25,0.5,0.75,0.9,1,1  1000 10000 100000 1000000

```


To benchmark Lean
run 
```bash
time ./.lake/build/bin/bench
```

To benchmark C

run 
```bash
time ./src/c/run.sh
```