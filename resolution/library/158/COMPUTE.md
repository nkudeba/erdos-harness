
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
