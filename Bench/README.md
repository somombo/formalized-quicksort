run 
`lake build hoaretest &&  lake build lomutotest`

and then

`time ./.lake/build/bin/hoaretest && time ./.lake/build/bin/lomutotest`

OR 
``` Measure-Command { .\.lake\build\bin\hoaretest.exe | Out-Default } && Measure-Command {  .\.lake\build\bin\lomutotest.exe | Out-Default }```


Try and adapt https://github.com/leanprover/lean4/tree/master/tests/bench/mergeSort 
benchmarking code to this