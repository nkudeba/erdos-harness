
## Long computation deep/long_pyr21.py (2026-10-16 09:26 UTC)
What it decides, in the session's words: P(21) exactly (exhaustive up to 8.96e13; also re-derives P(20) at 6× scale), with a witness chain and exact H via the Pratt recursion
Process: completed, exit 0, 992 s of 5400 s allowed. A completed process is evidence, not a result: certify anything it found before claiming it.
Last output:
```
PARI stack size set to 3000000000 bytes, maximum size set to 3000008704
t=2 Y_t=170898437 |R_t|=9550460 smallest=[3, 5, 7] time=0
t=3 Y_t=341796875 |R_t|=18386265 smallest=[7, 11, 13] time=3
t=4 Y_t=683593750 |R_t|=35445499 smallest=[23, 29, 43] time=9
t=5 Y_t=1367187500 |R_t|=67947538 smallest=[47, 59, 107] time=21
t=6 Y_t=2734375000 |R_t|=114614331 smallest=[283, 347, 359] time=47
t=7 Y_t=5468750000 |R_t|=137652678 smallest=[719, 1319, 1439] time=108
  t=8 seg 50 of 55 time=209
t=8 Y_t=10937500000 |R_t|=115942544 smallest=[1439, 2879, 4079] time=227
  t=9 seg 50 of 110 time=275
  t=9 seg 100 of 110 time=375
t=9 Y_t=21875000000 |R_t|=74019078 smallest=[2879, 20147, 25903] time=400
  t=10 seg 50 of 219 time=433
  t=10 seg 100 of 219 time=475
  t=10 seg 150 of 219 time=532
  t=10 seg 200 of 219 time=602
t=10 Y_t=43750000000 |R_t|=38050645 smallest=[34549, 65267, 86371] time=633
  t=11 batch done, time=654
  t=11 batch done, time=671
  t=11 batch done, time=689
  t=11 batch done, time=707
  t=11 batch done, time=725
  t=11 batch done, time=743
  t=11 batch done, time=761
  t=11 batch done, time=781
  t=11 batch done, time=801
  t=11 batch done, time=828
t=11 Y_t=87500000000 |R_t|=16562659 smallest=[138197, 207227, 621679] time=865
  t=12 batch done, time=884
  t=12 batch done, time=901
  t=12 batch done, time=918
  t=12 batch done, time=941
t=12 Y_t=175000000000 |R_t|=6316208 smallest=[1266767, 1520159, 1827479] time=952
  t=13 batch done, time=969
t=13 Y_t=350000000000 |R_t|=2147208 smallest=[14619833, 14920303, 18224639] time=980
t=14 Y_t=700000000000 |R_t|=640561 smallest=[36449279, 53065907, 59681213] time=989
t=15 Y_t=1400000000000 |R_t|=163690 smallest=[377982107, 437391349, 716174549] time=991
t=16 Y_t=2800000000000 |R_t|=35725 smallest=[1432349099, 1749565397, 2771868719] time=991
t=17 Y_t=5600000000000 |R_t|=6833 smallest=[22111003847, 25782283783, 27280026239] time=991
t=18 Y_t=11200000000000 |R_t|=1212 smallest=[54560052479, 110874748763, 136132234559] time=991
t=19 Y_t=22400000000000 |R_t|=214 smallest=[619108107719, 654720629749, 859409458847] time=991
t=20 Y_t=44800000000000 |R_t|=24 smallest=[7242080052479, 14403853854463, 19641618892471] time=991
t=21 Y_t=89600000000000 |R_t|=3 smallest=[64750853277599, 70643220056567, 85301359593119] time=991
RESULT: P(20)=7242080052479 (H=20, witness [2, 3, 7, 127, 509, 1019, 2039, 4079, 32633, 65267, 913739, 1827479, 109648741, 1315784893, 5263139573, 452630003279, 905260006559, 1810520013119, 3621040026239, 7242080052479]); P(21)=64750853277599 (H=21, witness [2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 207227, 7874627, 346483589, 692967179, 1385934359, 2771868719, 55437374381, 110874748763, 16187713319399, 32375426638799, 64750853277599]); exact ranges Y_t = 44800000000000, 89600000000000

```

## Long computation deep/long_gp_p20.py (2026-10-16 09:33 UTC)
What it decides, in the session's words: independent GP reproduction of min R_20(7.36e12) = P(20) = 7242080052479
Process: completed, exit 0, 390 s of 3600 s allowed. A completed process is evidence, not a result: certify anything it found before claiming it.
Last output:
```
PARI stack size set to 4000000000 bytes, maximum size set to 4000006144
t=2 1745876
t=3 Y_t=56152343 |R_t|=3346910 min=7 time=21
t=4 Y_t=112304687 |R_t|=6426921 min=23 time=54
t=5 Y_t=224609375 |R_t|=12181874 min=47 time=104
t=6 Y_t=449218750 |R_t|=19415482 min=283 time=173
t=7 Y_t=898437500 |R_t|=21511431 min=719 time=251
t=8 Y_t=1796875000 |R_t|=16865595 min=1439 time=314
t=9 Y_t=3593750000 |R_t|=10115358 min=2879 time=353
t=10 Y_t=7187500000 |R_t|=4913335 min=34549 time=375
t=11 Y_t=14375000000 |R_t|=2035563 min=138197 time=384
t=12 Y_t=28750000000 |R_t|=745476 min=1266767 time=388
t=13 Y_t=57500000000 |R_t|=242598 min=14619833 time=389
t=14 Y_t=115000000000 |R_t|=68237 min=36449279 time=390
t=15 Y_t=230000000000 |R_t|=16114 min=377982107 time=390
t=16 Y_t=460000000000 |R_t|=3168 min=1432349099 time=390
t=17 Y_t=920000000000 |R_t|=552 min=22111003847 time=390
t=18 Y_t=1840000000000 |R_t|=94 min=54560052479 time=390
t=19 Y_t=3680000000000 |R_t|=14 min=619108107719 time=390
t=20 Y_t=7360000000000 |R_t|=1 min=7242080052479 time=390
RESULT: GP pyramid: min R_20(Y_20=7360000000000) = 7242080052479; min R_19(Y_19=3680000000000) = 619108107719 (agrees with P(20)=7242080052479)

```
