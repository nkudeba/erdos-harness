
## Long computation deep/long_chain.py (2026-10-17 22:49 UTC)
What it decides, in the session's words: continues the exact F(N) chain from the certified F(1..53), at N = 54, 55, … with Kissat on 16 cubes per N. It prints every cube and the witnesses at the jumps, and ends with a RESULT line (an incomplete N is reported as INCOMPLETE). Expected reach is N ≈ 56–58.
Process: completed, exit 0, 6907 s of 7200 s allowed. A completed process is evidence, not a result: certify anything it found before claiming it.
Last output:
```
  N 54 k 16 cube 0 UNSAT 0.0
  N 54 k 16 cube 1 UNSAT 37.1
  N 54 k 16 cube 2 UNSAT 35.2
  N 54 k 16 cube 3 UNSAT 7.9
  N 54 k 16 cube 4 UNSAT 37.1
  N 54 k 16 cube 5 UNSAT 8.0
  N 54 k 16 cube 6 UNSAT 8.0
  N 54 k 16 cube 7 UNSAT 1.2
  N 54 k 16 cube 8 UNSAT 0.0
  N 54 k 16 cube 9 UNSAT 10.2
  N 54 k 16 cube 10 UNSAT 10.7
  N 54 k 16 cube 11 UNSAT 1.8
  N 54 k 16 cube 12 UNSAT 10.4
  N 54 k 16 cube 13 UNSAT 2.0
  N 54 k 16 cube 14 UNSAT 1.3
  N 54 k 16 cube 15 UNSAT 0.0
N 54 F 15 UNSAT t 171.0 total 171 
  N 55 k 16 cube 0 UNSAT 0.0
  N 55 k 16 cube 1 UNSAT 60.0
  N 55 k 16 cube 2 UNSAT 52.9
  N 55 k 16 cube 3 UNSAT 12.1
  N 55 k 16 cube 4 UNSAT 57.2
  N 55 k 16 cube 5 UNSAT 16.2
  N 55 k 16 cube 6 UNSAT 15.0
  N 55 k 16 cube 7 UNSAT 3.1
  N 55 k 16 cube 8 UNSAT 50.1
  N 55 k 16 cube 9 UNSAT 14.6
  N 55 k 16 cube 10 UNSAT 16.4
  N 55 k 16 cube 11 UNSAT 3.0
  N 55 k 16 cube 12 UNSAT 14.3
  N 55 k 16 cube 13 UNSAT 3.6
  N 55 k 16 cube 14 UNSAT 2.2
  N 55 k 16 cube 15 UNSAT 0.0
N 55 F 15 UNSAT t 320.7 total 492 
  N 56 k 16 cube 0 UNSAT 59.4
  N 56 k 16 cube 1 UNSAT 113.1
  N 56 k 16 cube 2 UNSAT 118.5
  N 56 k 16 cube 3 UNSAT 25.8
  N 56 k 16 cube 4 UNSAT 104.7
  N 56 k 16 cube 5 UNSAT 26.5
  N 56 k 16 cube 6 UNSAT 30.9
  N 56 k 16 cube 7 UNSAT 4.7
  N 56 k 16 cube 8 UNSAT 108.5
  N 56 k 16 cube 9 UNSAT 31.4
  N 56 k 16 cube 10 UNSAT 34.2
  N 56 k 16 cube 11 UNSAT 5.9
  N 56 k 16 cube 12 UNSAT 25.5
  N 56 k 16 cube 13 UNSAT 5.7
  N 56 k 16 cube 14 UNSAT 4.5
  N 56 k 16 cube 15 UNSAT 0.0
N 56 F 15 UNSAT t 699.2 total 1191 
  N 57 k 16 cube 0 UNSAT 161.2
  N 57 k 16 cube 1 UNSAT 148.6
  N 57 k 16 cube 2 UNSAT 148.2
  N 57 k 16 cube 3 UNSAT 34.1
  N 57 k 16 cube 4 UNSAT 168.6
  N 57 k 16 cube 5 UNSAT 39.0
  N 57 k 16 cube 6 UNSAT 39.2
  N 57 k 16 cube 7 UNSAT 6.0
  N 57 k 16 cube 8 UNSAT 143.4
  N 57 k 16 cube 9 UNSAT 41.7
  N 57 k 16 cube 10 UNSAT 38.9
  N 57 k 16 cube 11 UNSAT 7.6
  N 57 k 16 cube 12 UNSAT 36.9
  N 57 k 16 cube 13 UNSAT 8.2
  N 57 k 16 cube 14 UNSAT 6.1
  N 57 k 16 cube 15 UNSAT 0.0
N 57 F 15 UNSAT t 1027.7 total 2219 
  N 58 k 16 cube 0 UNSAT 418.6
  N 58 k 16 cube 1 UNSAT 283.5
  N 58 k 16 cube 2 UNSAT 312.3
  N 58 k 16 cube 3 UNSAT 53.2
  N 58 k 16 cube 4 UNSAT 276.5
  N 58 k 16 cube 5 UNSAT 64.2
  N 58 k 16 cube 6 UNSAT 72.7
  N 58 k 16 cube 7 UNSAT 10.2
  N 58 k 16 cube 8 UNSAT 279.2
  N 58 k 16 cube 9 UNSAT 65.4
  N 58 k 16 cube 10 UNSAT 76.9
  N 58 k 16 cube 11 UNSAT 12.9
  N 58 k 16 cube 12 UNSAT 61.7
  N 58 k 16 cube 13 SAT 6.1
N 58 F 16 SAT t 1993.5 total 4212 [1, 2, 4, 5, 17, 20, 22, 25, 29, 35, 44, 46, 51, 52, 57, 58]
  N 59 k 17 cube 0 UNSAT 0.0
  N 59 k 17 cube 1 UNSAT 9.2
  N 59 k 17 cube 2 UNSAT 0.0
  N 59 k 17 cube 3 UNSAT 2.5
  N 59 k 17 cube 4 UNSAT 0.0
  N 59 k 17 cube 5 UNSAT 5.2
  N 59 k 17 cube 6 UNSAT 0.0
  N 59 k 17 cube 7 UNSAT 0.4
  N 59 k 17 cube 8 UNSAT 0.0
  N 59 k 17 cube 9 UNSAT 4.6
  N 59 k 17 cube 10 UNSAT 0.0
  N 59 k 17 cube 11 UNSAT 0.8
  N 59 k 17 cube 12 UNSAT 0.0
  N 59 k 17 cube 13 UNSAT 1.0
  N 59 k 17 cube 14 UNSAT 0.0
  N 59 k 17 cube 15 UNSAT 0.0
N 59 F 16 UNSAT t 23.7 total 4236 
  N 60 k 17 cube 0 UNSAT 0.0
  N 60 k 17 cube 1 UNSAT 50.4
  N 60 k 17 cube 2 UNSAT 54.5
  N 60 k 17 cube 3 UNSAT 11.2
  N 60 k 17 cube 4 UNSAT 0.0
  N 60 k 17 cube 5 UNSAT 16.1
  N 60 k 17 cube 6 UNSAT 15.4
  N 60 k 17 cube 7 UNSAT 1.5
  N 60 k 17 cube 8 UNSAT 0.0
  N 60 k 17 cube 9 UNSAT 21.8
  N 60 k 17 cube 10 UNSAT 24.3
  N 60 k 17 cube 11 UNSAT 2.4
  N 60 k 17 cube 12 UNSAT 0.0
  N 60 k 17 cube 13 UNSAT 3.9
  N 60 k 17 cube 14 UNSAT 2.7
  N 60 k 17 cube 15 UNSAT 0.0
N 60 F 16 UNSAT t 204.1 total 4440 
  N 61 k 17 cube 0 UNSAT 0.0
  N 61 k 17 cube 1 UNSAT 103.0
  N 61 k 17 cube 2 UNSAT 114.5
  N 61 k 17 cube 3 UNSAT 32.0
  N 61 k 17 cube 4 UNSAT 123.9
  N 61 k 17 cube 5 UNSAT 27.3
  N 61 k 17 cube 6 UNSAT 26.7
  N 61 k 17 cube 7 UNSAT 3.6
  N 61 k 17 cube 8 UNSAT 0.0
  N 61 k 17 cube 9 UNSAT 37.3
  N 61 k 17 cube 10 UNSAT 41.2
  N 61 k 17 cube 11 UNSAT 6.4
  N 61 k 17 cube 12 UNSAT 37.2
  N 61 k 17 cube 13 UNSAT 6.4
  N 61 k 17 cube 14 UNSAT 4.5
  N 61 k 17 cube 15 UNSAT 0.0
N 61 F 16 UNSAT t 564.1 total 5004 
  N 62 k 17 cube 0 UNSAT 0.0
  N 62 k 17 cube 1 UNSAT 186.6
  N 62 k 17 cube 2 UNSAT 222.4
  N 62 k 17 cube 3 UNSAT 63.3
  N 62 k 17 cube 4 UNSAT 196.9
  N 62 k 17 cube 5 UNSAT 62.4
  N 62 k 17 cube 6 UNSAT 65.8
  N 62 k 17 cube 7 UNSAT 10.6
  N 62 k 17 cube 8 UNSAT 208.8
  N 62 k 17 cube 9 UNSAT 67.3
  N 62 k 17 cube 10 UNSAT 85.0
  N 62 k 17 cube 11 UNSAT 11.8
  N 62 k 17 cube 12 UNSAT 67.6
  N 62 k 17 cube 13 UNSAT 12.9
  N 62 k 17 cube 14 UNSAT 8.0
  N 62 k 17 cube 15 UNSAT 0.0
N 62 F 16 UNSAT t 1269.5 total 6274 
  N 63 k 17 cube 0 UNSAT 220.9
  N 63 k 17 cube 1 UNSAT 412.6
N 63 INCOMPLETE (deadline) after cubes 0..1
RESULT: F(1..62) = 1,2,3,4,4,5,5,6,6,6,7,7,7,8,8,8,8,9,9,9,9,10,10,10,10,10,11,11,11,11,12,12,12,12,12,12,13,13,13,13,13,13,13,14,14,14,14,14,14,14,15,15,15,15,15,15,15,16,16,16,16,16
RESULT jumps (k: first N, witness): {15: (51, [1, 2, 7, 8, 11, 17, 19, 20, 23, 37, 42, 44, 47, 49, 51]), 16: (58, [1, 2, 4, 5, 17, 20, 22, 25, 29, 35, 44, 46, 51, 52, 57, 58])}

```

## Long computation marathon-1/long_profile.py (2026-10-18 02:08 UTC)
What it decides, in the session's words: per-cube kissat times for N = 55, 56, 57 at b = 8 cube bits (k = 16), evidence (not certificate) for F(55..57) = 15; N = 56, 57 conditional on F(55), F(56) = 15 used in windows.
Process: completed, exit 0, 2971 s of 7200 s allowed. A completed process is evidence, not a result: certify anything it found before claiming it.
Last output:
```
N 55 q 15 cum 106.0 elapsed 106
N 55 q 31 cum 177.9 elapsed 178
N 55 q 47 cum 247.6 elapsed 248
N 55 q 63 cum 276.9 elapsed 277
N 55 q 79 cum 348.8 elapsed 349
N 55 q 95 cum 385.4 elapsed 386
N 55 q 111 cum 420.7 elapsed 421
N 55 q 127 cum 437.2 elapsed 438
N 55 q 143 cum 509.3 elapsed 510
N 55 q 159 cum 545.4 elapsed 546
N 55 q 175 cum 579.5 elapsed 580
N 55 q 191 cum 595.4 elapsed 596
N 55 q 207 cum 629.9 elapsed 631
N 55 q 223 cum 644.4 elapsed 645
N 55 q 239 cum 661.3 elapsed 663
N 55 q 255 cum 668.3 elapsed 670
TIMES 55 8 [0.0, 10.6, 10.0, 7.1, 10.5, 8.6, 7.2, 4.2, 11.5, 8.1, 8.9, 3.8, 8.2, 3.7, 3.6, 0.0, 0.0, 8.2, 9.4, 4.1, 9.0, 4.1, 4.6, 2.8, 9.2, 4.8, 4.0, 2.6, 3.8, 2.7, 2.6, 0.0, 0.0, 9.1, 9.0, 4.3, 9.3, 4.0, 3.6, 2.5, 8.8, 4.0, 5.3, 2.6, 4.3, 2.9, 0.0, 0.0, 0.0, 4.6, 4.0, 2.7, 4.2, 0.0, 2.7, 0.0, 3.6, 2.6, 2.6, 0.0, 2.3, 0.0, 0.0, 0.0, 0.0, 9.5, 9.0, 4.7, 9.0, 3.9, 4.0, 2.6, 8.3, 3.9, 4.7, 2.4, 4.6, 2.8, 2.5, 0.0, 0.0, 4.0, 4.8, 2.8, 3.7, 2.7, 2.7, 2.3, 3.5, 2.6, 2.8, 2.1, 2.6, 0.0, 0.0, 0.0, 0.0, 5.0, 4.0, 3.0, 4.7, 2.7, 2.4, 2.2, 3.6, 2.5, 2.6, 0.0, 2.6, 0.0, 0.0, 0.0, 0.0, 2.6, 2.5, 0.0, 2.2, 0.0, 2.2, 0.0, 2.4, 2.3, 2.3, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 9.0, 9.4, 4.0, 8.3, 4.2, 3.9, 2.6, 9.6, 4.7, 4.5, 2.7, 4.2, 2.5, 2.5, 0.0, 0.0, 4.1, 3.6, 2.3, 4.9, 2.7, 2.7, 2.2, 4.4, 2.9, 3.9, 2.3, 0.0, 0.0, 0.1, 0.0, 0.0, 4.1, 4.2, 3.0, 4.2, 2.6, 2.6, 2.2, 4.0, 2.5, 0.0, 0.0, 2.5, 2.2, 0.0, 0.0, 0.0, 3.1, 2.9, 2.2, 3.0, 0.0, 0.0, 0.0, 2.5, 2.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 4.7, 4.2, 2.9, 4.2, 2.5, 2.5, 2.2, 4.0, 0.0, 2.5, 0.0, 2.6, 0.0, 2.2, 0.0, 0.0, 2.5, 2.7, 2.2, 2.6, 0.0, 0.0, 0.0, 2.3, 0.0, 2.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2.7, 2.6, 0.0, 2.4, 2.2, 2.3, 0.0, 2.4, 0.0, 0.0, 0.0, 2.3, 0.0, 0.0, 0.0, 0.0, 2.3, 2.4, 0.0, 2.3, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
N 56 q 15 cum 188.5 elapsed 858
N 56 q 31 cum 304.3 elapsed 974
N 56 q 47 cum 404.9 elapsed 1075
N 56 q 63 cum 456.2 elapsed 1127
N 56 q 79 cum 556.3 elapsed 1227
N 56 q 95 cum 610.6 elapsed 1281
N 56 q 111 cum 655.2 elapsed 1326
N 56 q 127 cum 677.3 elapsed 1348
N 56 q 143 cum 783.8 elapsed 1455
N 56 q 159 cum 839.1 elapsed 1510
N 56 q 175 cum 883.0 elapsed 1555
N 56 q 191 cum 904.0 elapsed 1576
N 56 q 207 cum 947.8 elapsed 1620
N 56 q 223 cum 967.8 elapsed 1640
N 56 q 239 cum 985.5 elapsed 1658
N 56 q 255 cum 994.8 elapsed 1668
TIMES 56 8 [0.0, 19.7, 24.3, 11.5, 22.5, 13.3, 12.8, 5.3, 21.1, 12.8, 14.7, 5.9, 13.5, 5.9, 5.2, 0.0, 19.7, 11.7, 13.3, 5.3, 11.6, 4.7, 6.3, 3.4, 12.8, 6.9, 5.5, 3.2, 5.4, 2.9, 3.1, 0.0, 0.0, 13.9, 13.7, 5.8, 13.0, 5.8, 6.0, 2.9, 14.8, 5.5, 6.7, 3.0, 6.1, 3.4, 0.0, 0.0, 13.2, 6.5, 5.6, 3.3, 6.0, 0.0, 3.4, 0.0, 4.9, 2.9, 3.0, 0.0, 2.5, 0.0, 0.0, 0.0, 0.0, 14.1, 12.9, 5.9, 13.7, 5.3, 5.3, 3.1, 13.1, 5.7, 6.0, 2.7, 5.9, 3.3, 3.1, 0.0, 12.0, 5.1, 6.5, 2.8, 4.2, 2.6, 2.8, 2.4, 4.9, 2.8, 3.2, 2.2, 2.8, 0.0, 0.0, 0.0, 0.0, 7.6, 5.4, 3.5, 6.0, 2.7, 2.7, 2.4, 4.6, 2.9, 3.2, 0.0, 3.6, 0.0, 0.0, 0.0, 4.5, 3.1, 2.5, 0.0, 2.5, 0.0, 2.3, 0.0, 2.5, 2.3, 2.4, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 14.4, 15.4, 5.8, 13.2, 5.7, 5.8, 3.1, 14.9, 6.3, 6.6, 3.3, 6.1, 3.0, 2.9, 0.0, 12.9, 5.3, 4.8, 2.5, 6.7, 2.8, 3.2, 2.3, 6.3, 3.4, 2.9, 2.2, 0.0, 0.0, 0.0, 0.0, 0.0, 6.1, 6.7, 3.2, 6.0, 2.8, 3.0, 2.3, 6.1, 2.7, 0.0, 0.0, 2.7, 2.3, 0.0, 0.0, 4.8, 2.8, 3.0, 2.4, 3.2, 0.0, 0.0, 0.0, 2.5, 2.3, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 6.8, 6.2, 3.6, 5.6, 2.7, 2.6, 2.3, 6.0, 0.0, 2.8, 0.0, 3.0, 0.0, 2.2, 0.0, 4.7, 2.9, 2.8, 2.2, 2.6, 0.0, 0.0, 0.0, 2.5, 0.0, 2.3, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3.1, 2.8, 0.0, 2.4, 2.3, 2.3, 0.0, 2.5, 0.0, 0.0, 0.0, 2.3, 0.0, 0.0, 0.0, 2.4, 2.3, 2.4, 0.0, 2.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
N 57 q 15 cum 254.5 elapsed 1923
N 57 q 31 cum 412.8 elapsed 2081
N 57 q 47 cum 565.2 elapsed 2233
N 57 q 63 cum 625.6 elapsed 2294
N 57 q 79 cum 754.8 elapsed 2423
N 57 q 95 cum 823.6 elapsed 2492
N 57 q 111 cum 889.8 elapsed 2558
N 57 q 127 cum 914.1 elapsed 2583
N 57 q 143 cum 1043.1 elapsed 2712
N 57 q 159 cum 1108.6 elapsed 2777
N 57 q 175 cum 1171.3 elapsed 2840
N 57 q 191 cum 1195.2 elapsed 2864
N 57 q 207 cum 1245.0 elapsed 2914
N 57 q 223 cum 1268.3 elapsed 2937
N 57 q 239 cum 1291.8 elapsed 2961
N 57 q 255 cum 1301.5 elapsed 2971
TIMES 57 8 [0.0, 30.6, 33.7, 15.1, 30.1, 18.4, 16.2, 6.5, 31.8, 16.6, 18.1, 6.9, 16.2, 7.9, 6.4, 0.0, 30.3, 17.7, 18.6, 6.7, 17.8, 6.9, 7.2, 4.1, 16.7, 8.7, 6.8, 3.6, 5.9, 3.7, 3.6, 0.0, 29.7, 17.8, 16.2, 6.9, 18.4, 6.8, 6.8, 3.1, 17.8, 6.5, 8.1, 3.6, 7.1, 3.6, 0.0, 0.0, 16.7, 8.6, 5.8, 3.6, 7.8, 0.0, 3.6, 0.0, 5.2, 3.4, 3.1, 0.0, 2.6, 0.0, 0.0, 0.0, 0.0, 17.2, 18.9, 6.9, 19.2, 6.8, 6.1, 3.1, 17.0, 7.2, 8.6, 3.2, 7.9, 3.9, 3.2, 0.0, 16.7, 7.0, 8.7, 3.3, 6.1, 3.2, 3.4, 2.5, 5.9, 3.3, 3.4, 2.3, 3.0, 0.0, 0.0, 0.0, 14.6, 7.9, 7.0, 3.9, 6.8, 3.6, 2.7, 2.5, 6.6, 3.2, 3.6, 0.0, 3.8, 0.0, 0.0, 0.0, 5.9, 3.3, 2.8, 0.0, 2.7, 0.0, 2.3, 0.0, 2.5, 2.4, 2.4, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 18.3, 18.4, 7.2, 16.4, 7.6, 7.1, 3.5, 17.3, 8.5, 7.6, 3.8, 6.9, 3.3, 3.1, 0.0, 16.1, 7.0, 6.0, 2.7, 8.4, 3.3, 3.2, 2.4, 7.5, 3.5, 3.1, 2.3, 0.0, 0.0, 0.0, 0.0, 15.3, 6.4, 7.2, 3.6, 6.9, 3.0, 3.0, 2.5, 6.3, 3.0, 0.0, 0.0, 3.0, 2.5, 0.0, 0.0, 5.9, 3.2, 3.1, 2.3, 4.1, 0.0, 0.0, 0.0, 2.9, 2.4, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 9.0, 6.7, 3.4, 6.8, 3.0, 2.8, 2.4, 6.7, 0.0, 3.2, 0.0, 3.5, 0.0, 2.3, 0.0, 6.4, 3.3, 3.1, 2.3, 3.1, 0.0, 0.0, 0.0, 2.8, 0.0, 2.3, 0.0, 0.0, 0.0, 0.0, 0.0, 4.7, 3.5, 2.9, 0.0, 2.6, 2.3, 2.4, 0.0, 2.8, 0.0, 0.0, 0.0, 2.3, 0.0, 0.0, 0.0, 2.6, 2.4, 2.3, 0.0, 2.4, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
RESULT: [(55, 'UNSAT', 668.3), (56, 'UNSAT', 994.8), (57, 'UNSAT', 1301.5)]

```

## Long computation marathon-2/long_profile56.py (2026-10-18 02:37 UTC)
What it decides, in the session's words: exact CaDiCaL search with the checker CNF for N = 56 then N = 57 (k = 16, 256 cubes each), with per-cube times. Evidence for F(56) = F(57) = 15 (N = 57 assumes F(56) = 15 in its windows) and a packing profile for future checkers. NOT a certificate.
Process: completed, exit 0, 1764 s of 7200 s allowed. A completed process is evidence, not a result: certify anything it found before claiming it.
Last output:
```
N 56 k 16 cubes 0 .. 15 times [0.0, 23.9, 24.8, 10.3, 22.2, 10.9, 13.9, 3.5, 25.1, 14.0, 13.7, 4.0, 13.7, 3.5, 3.0, 0.0] elapsed 187
N 56 k 16 cubes 16 .. 31 times [22.4, 11.4, 14.6, 3.0, 11.0, 2.6, 4.3, 1.0, 15.0, 4.9, 3.9, 1.1, 2.6, 1.1, 1.1, 0.0] elapsed 287
N 56 k 16 cubes 32 .. 47 times [0.0, 12.6, 11.9, 3.4, 12.7, 3.4, 4.1, 0.8, 14.7, 3.9, 5.1, 0.9, 4.1, 1.1, 0.0, 0.0] elapsed 366
N 56 k 16 cubes 48 .. 63 times [13.1, 4.2, 3.1, 1.3, 4.2, 0.0, 1.4, 0.0, 3.1, 0.8, 0.9, 0.0, 0.6, 0.0, 0.0, 0.0] elapsed 399
N 56 k 16 cubes 64 .. 79 times [0.0, 12.4, 12.2, 4.0, 12.4, 3.0, 3.4, 0.9, 13.2, 4.0, 4.3, 0.7, 4.0, 1.3, 1.0, 0.0] elapsed 475
N 56 k 16 cubes 80 .. 95 times [10.4, 3.4, 4.8, 0.9, 2.8, 0.6, 0.9, 0.2, 3.1, 0.8, 1.2, 0.2, 0.7, 0.0, 0.0, 0.0] elapsed 505
N 56 k 16 cubes 96 .. 111 times [0.0, 4.5, 4.0, 1.5, 4.1, 1.0, 0.8, 0.3, 3.9, 1.0, 1.2, 0.0, 1.2, 0.0, 0.0, 0.0] elapsed 529
N 56 k 16 cubes 112 .. 127 times [2.6, 1.0, 0.7, 0.0, 0.4, 0.0, 0.2, 0.0, 0.3, 0.2, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 535
N 56 k 16 cubes 128 .. 143 times [0.0, 14.5, 15.4, 4.3, 13.4, 3.6, 3.6, 1.3, 13.7, 4.2, 4.5, 1.2, 4.1, 0.9, 0.8, 0.0] elapsed 620
N 56 k 16 cubes 144 .. 159 times [12.7, 3.9, 3.1, 0.5, 4.5, 0.9, 1.1, 0.2, 3.9, 1.2, 0.8, 0.2, 0.0, 0.0, 0.0, 0.0] elapsed 653
N 56 k 16 cubes 160 .. 175 times [0.0, 4.2, 4.3, 1.3, 3.8, 0.9, 1.1, 0.2, 3.6, 0.7, 0.0, 0.0, 0.6, 0.2, 0.0, 0.0] elapsed 674
N 56 k 16 cubes 176 .. 191 times [3.5, 0.9, 1.0, 0.2, 1.3, 0.0, 0.0, 0.0, 0.7, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 682
N 56 k 16 cubes 192 .. 207 times [0.0, 4.5, 3.9, 1.5, 3.9, 0.9, 0.6, 0.2, 3.7, 0.0, 0.8, 0.0, 1.2, 0.0, 0.2, 0.0] elapsed 704
N 56 k 16 cubes 208 .. 223 times [3.5, 0.7, 0.9, 0.2, 0.8, 0.0, 0.0, 0.0, 0.7, 0.0, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 711
N 56 k 16 cubes 224 .. 239 times [0.0, 1.0, 0.8, 0.0, 0.5, 0.2, 0.1, 0.0, 0.5, 0.0, 0.0, 0.0, 0.1, 0.0, 0.0, 0.0] elapsed 715
N 56 k 16 cubes 240 .. 255 times [0.3, 0.2, 0.1, 0.0, 0.1, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 716
N 57 k 16 cubes 0 .. 15 times [0.0, 35.9, 38.8, 14.7, 36.4, 18.5, 16.9, 4.5, 31.6, 18.4, 17.1, 4.9, 15.7, 5.5, 4.3, 0.0] elapsed 979
N 57 k 16 cubes 16 .. 31 times [35.7, 17.0, 19.7, 5.1, 16.7, 4.8, 6.3, 2.4, 16.6, 5.6, 4.9, 1.9, 4.5, 2.2, 1.5, 0.0] elapsed 1124
N 57 k 16 cubes 32 .. 47 times [29.8, 17.0, 16.8, 4.7, 17.1, 4.8, 5.2, 1.2, 17.6, 4.6, 5.5, 1.5, 5.3, 1.8, 0.0, 0.0] elapsed 1257
N 57 k 16 cubes 48 .. 63 times [17.0, 5.8, 4.5, 1.5, 6.2, 0.0, 1.6, 0.0, 3.8, 1.2, 1.1, 0.0, 0.8, 0.0, 0.0, 0.0] elapsed 1301
N 57 k 16 cubes 64 .. 79 times [0.0, 17.9, 19.2, 5.3, 17.9, 4.9, 4.3, 1.5, 17.3, 5.1, 5.0, 1.2, 5.3, 2.0, 1.4, 0.0] elapsed 1409
N 57 k 16 cubes 80 .. 95 times [18.6, 4.7, 5.6, 1.3, 3.7, 1.0, 1.5, 0.4, 3.9, 1.5, 1.6, 0.3, 1.3, 0.0, 0.0, 0.0] elapsed 1454
N 57 k 16 cubes 96 .. 111 times [15.6, 5.4, 4.9, 2.3, 5.2, 1.5, 0.8, 0.4, 4.6, 1.5, 1.6, 0.0, 1.9, 0.0, 0.0, 0.0] elapsed 1500
N 57 k 16 cubes 112 .. 127 times [3.7, 1.3, 0.9, 0.0, 0.6, 0.0, 0.2, 0.0, 0.5, 0.2, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 1508
N 57 k 16 cubes 128 .. 143 times [0.0, 22.0, 20.2, 4.5, 18.1, 5.1, 4.6, 1.7, 20.8, 5.1, 4.7, 1.5, 5.1, 1.6, 1.2, 0.0] elapsed 1624
N 57 k 16 cubes 144 .. 159 times [16.0, 4.9, 3.8, 0.8, 5.4, 1.5, 1.3, 0.3, 5.3, 1.6, 1.1, 0.3, 0.0, 0.0, 0.0, 0.0] elapsed 1666
N 57 k 16 cubes 160 .. 175 times [15.5, 5.4, 4.6, 1.5, 4.6, 1.1, 1.2, 0.3, 3.6, 0.9, 0.0, 0.0, 0.8, 0.2, 0.0, 0.0] elapsed 1706
N 57 k 16 cubes 176 .. 191 times [4.3, 1.1, 1.2, 0.3, 1.9, 0.0, 0.0, 0.0, 0.9, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 1716
N 57 k 16 cubes 192 .. 207 times [0.0, 6.7, 4.9, 1.7, 4.6, 1.5, 0.8, 0.3, 4.9, 0.0, 1.1, 0.0, 1.5, 0.0, 0.2, 0.0] elapsed 1745
N 57 k 16 cubes 208 .. 223 times [4.1, 1.3, 1.3, 0.3, 1.3, 0.0, 0.0, 0.0, 1.0, 0.0, 0.3, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 1754
N 57 k 16 cubes 224 .. 239 times [3.0, 1.5, 1.0, 0.0, 0.6, 0.2, 0.2, 0.0, 0.8, 0.0, 0.0, 0.0, 0.2, 0.0, 0.0, 0.0] elapsed 1762
N 57 k 16 cubes 240 .. 255 times [0.4, 0.2, 0.1, 0.0, 0.2, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0] elapsed 1764
RESULT: {56: 'all 256 cubes UNSAT (716 s)', 57: 'all 256 cubes UNSAT (1048 s)'}

```
