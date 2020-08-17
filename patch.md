### Clarifications on test outputs

Test outputs now contain additional information to help clarify: 1) what is
being tested, 2) what is expected from the test, and 3) where the associated
claim is in the paper.

For example, consider the following outputs for the correct implementation and
an incorrect variant of the reportNoisyMax algorithm (abbreviated as `rnm`). The
test harness now prints the following.

```
> Test: rnm
> Expect: test to pass
> Paper reference: table on page 16, line 737, rnm column
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 0.8852153992735505]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 0.7648761993565646]
[Ok 1.459737916183364,Ok 2.0,Ok 0.7587791523787643]
[Ok 1.2096468491706178,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 1.9293545839212147]
[Ok 1.872487080836579,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 1.9914071748850726,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 1.1816143060170572,Ok 2.0,Ok 1.4105287317422224]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
+++ OK, passed 20 tests.
> Test: buggy rnm
> Expect: detects DP violation
> Paper reference: table on page 16, line 738, rnm column
[FailedUnSat ["|eps >= abs(2513663966521915 % 4503599627370496 + shift - (-230931334299229) % 4503599627370496) / 1 % 1!6|","|eps1 >= abs(1222502890986231 % 2251799813685248 + shift1 - 3303030686917533 % 4503599627370496) / 1 % 1!8|","|eps2 >= abs(557705314103441 % 4503599627370496 + shift2 - 635866397180015 % 1125899906842624) / 1 % 1!10|","|eps3 >= abs((-1744026685719329) % 4503599627370496 + shift3 - (-1177224656108169) % 4503599627370496) / 1 % 1!12|","|eps4 >= abs(1509397571218697 % 4503599627370496 + shift4 - 4502460340365891 % 4503599627370496) / 1 % 1!14|","|eps5 >= abs((-211077282124067) % 562949953421312 + shift5 - 25061779553923 % 1125899906842624) / 1 % 1!16|","|not(run_28_lap3 > (-230931334299229) % 4503599627370496)!506|","|abs(4421270169350377 % 9007199254740992 + shift3 - run_28_lap3) <= 1 % 1000000!515|","|not(run_31_lap5 > (-230931334299229) % 4503599627370496)!562|","|abs(100325634152321 % 281474976710656 + shift5 - run_31_lap5) <= 1 % 1000000!573|","|not(run_34_lap1 > (-230931334299229) % 4503599627370496)!612|","|abs(4174434664825307 % 9007199254740992 + shift1 - run_34_lap1) <= 1 % 1000000!619|","|not(run_38_lap3 > (-230931334299229) % 4503599627370496)!686|","|abs(1119966447398815 % 4503599627370496 + shift3 - run_38_lap3) <= 1 % 1000000!695|","|not(run_42_lap2 > (-230931334299229) % 4503599627370496)!757|","|abs(4732480705721883 % 9007199254740992 + shift2 - run_42_lap2) <= 1 % 1000000!765|","|not(run_45_lap4 > (-230931334299229) % 4503599627370496)!813|","|not(run_45_lap5 > (-230931334299229) % 4503599627370496)!814|","|abs(614945838212325 % 9007199254740992 + shift4 - run_45_lap4) <= 1 % 1000000!823|","|abs(1281237523042735 % 9007199254740992 + shift5 - run_45_lap5) <= 1 % 1000000!825|","|eps + (eps1 + eps2 + eps3 + (eps4 + eps5)) <= 2 % 1!846|"],Ok 1.7745940014301798,Ok 1.4081029668141671,Ok 2.0,Ok 2.0,Ok 2.0]
found a bug in 3.081404s, 1 iterations
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 0.8632682668852492,Ok 2.0]
[Ok 1.84603186653547,Ok 1.965474286370288,Ok 1.936791334359287,Ok 2.0]
[Ok 1.9189456925059867,Ok 2.0,Ok 2.0]
[FailedUnSat ["|eps >= abs(2796537599591711 % 4503599627370496 + shift - (-1579983074948685) % 4503599627370496) / 1 % 1!7|","|eps1 >= abs((-113087200927651) % 140737488355328 + shift1 - (-1977293580073159) % 4503599627370496) / 1 % 1!9|","|eps2 >= abs((-3397652104364079) % 4503599627370496 + shift2 - (-1437150863510555) % 1125899906842624) / 1 % 1!11|","|eps3 >= abs(505935802440933 % 4503599627370496 + shift3 - (-549558722387877) % 2251799813685248) / 1 % 1!13|","|eps4 >= abs(3610037555837163 % 4503599627370496 + shift4 - 880011062765645 % 2251799813685248) / 1 % 1!15|","|eps5 >= abs((-346527710365517) % 2251799813685248 + shift5 - 252443385693749 % 4503599627370496) / 1 % 1!17|","|eps6 >= abs((-3677472335129607) % 4503599627370496 + shift6 - (-40984812610445) % 35184372088832) / 1 % 1!19|","|not(run_6_lap4 > (-1579983074948685) % 4503599627370496)!129|","|abs(2274262524269747 % 9007199254740992 + shift4 - run_6_lap4) <= 1 % 1000000!140|","|not(run_11_lap6 > (-1579983074948685) % 4503599627370496)!236|","|abs(1791451507454037 % 4503599627370496 + shift6 - run_11_lap6) <= 1 % 1000000!249|","|not(run_17_lap3 > (-1579983074948685) % 4503599627370496)!359|","|abs(5520793304623181 % 9007199254740992 + shift3 - run_17_lap3) <= 1 % 1000000!369|","|not(run_34_lap1 > (-1579983074948685) % 4503599627370496)!714|","|abs(704919724348271 % 2251799813685248 + shift1 - run_34_lap1) <= 1 % 1000000!722|","|not(run_38_lap1 > (-1579983074948685) % 4503599627370496)!798|","|abs((-3304015074234531) % 9007199254740992 + shift1 - run_38_lap1) <= 1 % 1000000!806|","|not(run_41_lap5 > (-1579983074948685) % 4503599627370496)!865|","|abs(2192156728976119 % 18014398509481984 + shift5 - run_41_lap5) <= 1 % 1000000!877|","|not(run_43_lap2 > (-1579983074948685) % 4503599627370496)!904|","|not(run_43_lap4 > (-1579983074948685) % 4503599627370496)!906|","|abs(1246691148431439 % 2251799813685248 + shift2 - run_43_lap2) <= 1 % 1000000!913|","|abs(1216072253981161 % 2251799813685248 + shift4 - run_43_lap4) <= 1 % 1000000!917|","|eps + (eps1 + eps2 + eps3 + (eps4 + eps5 + eps6)) <= 2 % 1!924|"],Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
found a bug in 10.970922s, 5 iterations
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 1.241257466818064,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 0.8865716832373849,Ok 0.936514865530786,Ok 1.9039420223303312]
[FailedUnSat ["|eps >= abs(3525065190237265 % 4503599627370496 + shift - 1506675376911687 % 2251799813685248) / 1 % 1!5|","|eps1 >= abs((-4138724277978519) % 4503599627370496 + shift1 - (-268985532885983) % 4503599627370496) / 1 % 1!7|","|eps2 >= abs(75555772906985 % 1125899906842624 + shift2 - 1174055255077059 % 4503599627370496) / 1 % 1!9|","|eps3 >= abs(681626731973947 % 1125899906842624 + shift3 - 1384248763294809 % 1125899906842624) / 1 % 1!11|","|eps4 >= abs((-1833631016597163) % 2251799813685248 + shift4 - (-674251251004609) % 1125899906842624) / 1 % 1!13|","|not(run_6_lap4 > 1506675376911687 % 2251799813685248)!93|","|abs(3421751002295355 % 4503599627370496 + shift4 - run_6_lap4) <= 1 % 1000000!102|","|not(run_44_lap2 > 1506675376911687 % 2251799813685248)!661|","|abs(6491061013228949 % 9007199254740992 + shift2 - run_44_lap2) <= 1 % 1000000!668|","|not(run_47_lap1 > 1506675376911687 % 2251799813685248)!705|","|abs(2499577891223309 % 4503599627370496 + shift1 - run_47_lap1) <= 1 % 1000000!711|","|not(run_55_lap3 > 1506675376911687 % 2251799813685248)!827|","|abs(6809207089625405 % 9007199254740992 + shift3 - run_55_lap3) <= 1 % 1000000!835|","|not(run_81_lap2 > 1506675376911687 % 2251799813685248)!1216|","|abs(6864955285503095 % 9007199254740992 + shift2 - run_81_lap2) <= 1 % 1000000!1223|","|not(run_83_lap1 > 1506675376911687 % 2251799813685248)!1245|","|abs(2108954281230883 % 4503599627370496 + shift1 - run_83_lap1) <= 1 % 1000000!1251|","|eps + (0 % 1 + (eps1 + eps2 + eps3 + eps4)) <= 2 % 1!1290|"],Ok 1.5544335846744237,Ok 1.3955223100777574,Ok 1.0249495299706477,Ok 1.4409150354457587]
found a bug in 13.806216s, 5 iterations
[Ok 0.7591339690468679,Ok 0.8595841000705086,Ok 0.5763010633876815,Ok 1.1034795776507274]
[FailedUnSat ["|eps >= abs((-963284498061719) % 4503599627370496 + shift - (-2497349107201981) % 2251799813685248) / 1 % 1!3|","|eps1 >= abs((-255747168078639) % 1125899906842624 + shift1 - 1447115195348391 % 2251799813685248) / 1 % 1!5|","|eps2 >= abs(1186682521315079 % 2251799813685248 + shift2 - 6864726354657807 % 4503599627370496) / 1 % 1!7|","|not(run_23_lap1 > (-2497349107201981) % 2251799813685248)!207|","|abs((-4495879571074001) % 18014398509481984 + shift1 - run_23_lap1) <= 1 % 1000000!211|","|not(run_32_lap1 > (-2497349107201981) % 2251799813685248)!288|","|abs((-2493561765418547) % 9007199254740992 + shift1 - run_32_lap1) <= 1 % 1000000!292|","|not(run_37_lap2 > (-2497349107201981) % 2251799813685248)!334|","|abs((-4088376151930195) % 2251799813685248 + shift2 - run_37_lap2) <= 1 % 1000000!339|","|eps + (0 % 1 + (eps1 + eps2)) <= 2 % 1!342|"],Ok 1.0159588290964863,Ok 0.9655478918759455]
found a bug in 1.299147s, 2 iterations
[Ok 1.3101882937321916,Ok 1.3239587385290899,Ok 1.7549882869850635,Ok 1.4710663654792866,Ok 1.9514475402079616]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 1.8054151611596627,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 1.826871393116678,Ok 1.3250101445137492,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 1.8129042929915298,Ok 0.7326493518779795,Ok 1.7737783435608194]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 1.8817215805692287,Ok 1.0539960099305323,Ok 2.0,Ok 2.0,Ok 2.0]
[Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
[FailedUnSat ["|eps >= abs((-205390207613435) % 2251799813685248 + shift - (-4235219518799817) % 4503599627370496) / 1 % 1!6|","|eps1 >= abs((-491193256697261) % 4503599627370496 + shift1 - 2039976598692591 % 4503599627370496) / 1 % 1!8|","|eps2 >= abs(1361080192217041 % 2251799813685248 + shift2 - 482976882062649 % 4503599627370496) / 1 % 1!10|","|eps3 >= abs(731636680448231 % 4503599627370496 + shift3 - (-1741708975705985) % 4503599627370496) / 1 % 1!12|","|eps4 >= abs((-505620393379915) % 562949953421312 + shift4 - (-844307552744551) % 1125899906842624) / 1 % 1!14|","|eps5 >= abs(169629141040167 % 4503599627370496 + shift5 - 2265866675317231 % 2251799813685248) / 1 % 1!16|","|not(run_2_lap1 > (-4235219518799817) % 4503599627370496)!36|","|not(run_2_lap4 > (-4235219518799817) % 4503599627370496)!39|","|not(run_2_lap5 > (-4235219518799817) % 4503599627370496)!40|","|abs((-467273974327369) % 4503599627370496 + shift1 - run_2_lap1) <= 1 % 1000000!43|","|abs((-7789232211423335) % 9007199254740992 + shift4 - run_2_lap4) <= 1 % 1000000!49|","|abs((-1127521464582577) % 9007199254740992 + shift5 - run_2_lap5) <= 1 % 1000000!51|","|eps + (eps1 + eps2 + eps3 + (eps4 + eps5)) <= 2 % 1!54|"],Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0,Ok 2.0]
found a bug in 24.821094s, 9 iterations
+++ OK, passed 5 tests.
```
At the top, we have 3 lines containing the test name, the
expectation, and location of claim in the paper. For the `rnm` test, we are
checking a correct implementation of `rnm` does not trigger any differential
privacy violation. Each of the lines like `[Ok 2.0,Ok 2.0,Ok
0.8852153992735505]` contain the observed epsilon privacy parameter that Z3 was
able to derive.

Although these outputs are quite verbose, we feel it is important to include
them in the test harness, because 1) some of the tests run for a long time, and
these outputs provide incremental feedback on test progress; and 2) these
outputs also serve as a basic sanity check---since `rnm` is 2-DP, we expect all
observed privacy parameters to be at most 2, and that is indeed the case here.

For tests on buggy programs (for example, the `buggy rnm` test above), we expect
the test harness to consistently report differential privacy violations. For
these buggy programs, when a violation is detected, the test harness produces a
line that contains a `FailedUnSat` value, and this `FailedUnSat` value contains
the unsatisfiable core reported from Z3. Such unsat cores are also valuable
sanity checks for ensuring the test harness has indeed found something for which
FuzzDP cannot validate.

If reviewers prefer a test output that does not contain any of the incremental
outputs, the outputs of `stack test` can be piped into a file (say
`output.txt`), and running the following command will produce a reduced test output.
```bash
$ grep -vE '^\[' output.txt
> Test: rnm
> Expect: test to pass
> Paper reference: table on page 16, line 737, rnm column
+++ OK, passed 20 tests.
> Test: buggy rnm
> Expect: detects DP violation
> Paper reference: table on page 16, line 738, rnm column
found a bug in 3.081404s, 1 iterations
found a bug in 10.970922s, 5 iterations
found a bug in 13.806216s, 5 iterations
found a bug in 1.299147s, 2 iterations
found a bug in 24.821094s, 9 iterations
+++ OK, passed 5 tests.
```


### Instructions on applying the patch

The patch is a single file `Spec.hs` (md5 = `ea8d8edb4effac1beeef7481afda0ce2`). To apply the patch, please first start a
docker container for the FuzzDP image:
```bash
$ docker run -it --rm fuzz-dp:latest
```
Next, in your *host* shell, run the following command to determine the container id
```bash
$ docker ps -q
4f9e0226bd80 # your output may be different
```
Finally, in your *host* shell, run the following command to copy the downloaded
`Spec.hs` file into the container:
```bash
$ docker cp host/path/to/downloaded/Spec.hs 4f9e0226bd80:/tmp/fuzzi-model/test/
```

All of the instructions in the overview still apply, running `stack test` will
kick off the entire test suite with the updated test outputs described above.

#### Docker tips
Please note that due to the immutable nature of docker images, if the `fuzz-dp`
container is killed, and later restarted, then the patch needs to be re-applied.

If you prefer to persist patch into your local `fuzz-dp` docker image, please
run this command after applying the patch
```bash
# note that your container id will likely be different
$ docker container commit 4f9e0226bd80 fuzz-dp:patched
```

This will persist the patch to the `fuzz-dp` image under the `fuzz-dp:patched`
image. Now, you may kill the running container, and run
```bash
$ docker run -it --rm fuzz-dp:patched
```
to start the patched image, or
```bash
$ docker run -it --rm fuzz-dp:latest
```
to start the unpatched image.

### What was included in the patch

1. Additional outputs at the top of each test for clarification
2. Removed test size outputs to reduce clutter
3. Rearranged the order of tests, so that tests for the same algorithm run
   adjacent to each other

### Additional note

The original table in the overview that connects each test definition to the
benchmark table in the paper now has out-of-sync line numbers. Please refer to
the following updated table:

| Test name                                             | File:Line Number   | Evaluation | Correct | Buggy |
|-------------------------------------------------------|--------------------|------------|---------|-------|
| prop_simpleCountIsDifferentiallyPrivate               | `test/Spec.hs:566` | nc         | x       |       |
| prop_simpleCountEpsTooSmallIsNotDifferentiallyPrivate | `test/Spec.hs:570` | nc         |         | x     |
| prop_simpleMeanIsDifferentiallyPrivate                | `test/Spec.hs:574` | nm         | x       |       |
| prop_unboundedMeanIsNotDifferentiallyPrivate          | `test/Spec.hs:582` | nm         |         | x     |
| prop_simpleSumIsDifferentiallyPrivate                 | `test/Spec.hs:578` | ns         | x       |       |
| simpleSumBuggyNotPrivateTest                          | `test/Spec.hs:105` | ns         |         | x     |
| prop_prefixSumIsDifferentiallyPrivate                 | `test/Spec.hs:500` | ps         | x       |       |
| prefixSumBuggyNotPrivateTest                          | `test/Spec.hs:92`  | ps         |         | x     |
| prop_privTreeIsDifferentiallyPrivate                  | `test/Spec.hs:544` | pt         | x       |       |
| prop_privTreeBuggyIsNotDifferentiallyPrivate          | `test/Spec.hs:550` | pt         |         | x     |
| prop_rnmIsDifferentiallyPrivate                       | `test/Spec.hs:472` | rnm        | x       |       |
| prop_rnmBuggyIsNotDifferentiallyPrivate               | `test/Spec.hs:486` | rnm        |         | x     |
| prop_smartSumIsDifferentiallyPrivate                  | `test/Spec.hs:491` | ss         | x       |       |
| prop_smartSumBuggyIsNotDifferentiallyPrivate          | `test/Spec.hs:504` | ss         |         | x     |
| prop_sparseVectorIsDifferentiallyPrivate              | `test/Spec.hs:508` | sv         | x       |       |
| prop_sparseVectorBuggyIsNotDifferentiallyPrivate      | `test/Spec.hs:524` | sv         |         | x     |
| prop_sparseVectorBuggy4IsNotDifferentiallyPrivate     | `test/Spec.hs:532` | sv         |         | x     |
| prop_sparseVectorBuggy5IsNotDifferentiallyPrivate     | `test/Spec.hs:536` | sv         |         | x     |
| prop_sparseVectorBuggy6IsNotDifferentiallyPrivate     | `test/Spec.hs:540` | sv         |         | x     |
| prop_sparseVectorGapIsDifferentiallyPrivate           | `test/Spec.hs:558` | svGap      | x       |       |
| sparseVectorGapBuggyNotPrivateTest                    | `test/Spec.hs:322` | svGap      |         | x     |
