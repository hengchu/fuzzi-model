### Artifact Guide

FuzzDP is a Haskell package that provides an embedded programming language with
language primitives differential privacy, and an automatic testing framework
that checks differential privacy properties of languages written in the embedded
language.

#### Building FuzzDP with Docker

We have packaged FuzzDP and its external dependency `z3` into the provided
docker image. We also provide both `vim` and `emacs` text editors in the docker
image for modifying and experimenting with programs in the docker image.

1. Install Docker following the [official guide](https://docs.docker.com/install/)
2. Download the image *TODO* (provide link)
3. Start the docker daemon. Docker will ask for your host system credential on first time startup, and it may also show a login UI for dockerhub. However, you do *not* need to login for the following steps
4. Run `docker image load -i fuzzdp-artifact.tgz`, this may take a while to complete
5. Run `docker images`, and verify it shows an image with `REPOSITORY fuzz-dp`
6. Run `docker run --rm -it fuzz-dp`

#### Step-by-step guide

FuzzDP's build system is managed by the Haskell build tool `stack`. We use
`stack` to build, and also run the entire benchmark algorithm test suite.

To start, run `stack test` in the docker shell. This will run the entire test
suite for all benchmark algorithms listed in the paper. The entire process takes
around 70 minutes to complete on a 4.0GHz quad-core CPU (using only 1 core).

We also provide a detailed guide on writing your own differentiall private
program in FuzzDP and testing it at the detailed guide below.

#### Claims supported by this artifact

Here is a table that matches the benchmark test definitions with the FuzzDP
benchmark results table in the evaluation section.

| Test name                                             | File:Line Number   | Evaluation | Correct | Buggy |
|-------------------------------------------------------|--------------------|------------|---------|-------|
| prop_simpleCountIsDifferentiallyPrivate               | `test/Spec.hs:522` | nc         | x       |       |
| prop_simpleCountEpsTooSmallIsNotDifferentiallyPrivate | `test/Spec.hs:522` | nc         |         | x     |
| prop_simpleMeanIsDifferentiallyPrivate                | `test/Spec.hs:530` | nm         | x       |       |
| prop_unboundedMeanIsNotDifferentiallyPrivate          | `test/Spec.hs:534` | nm         |         | x     |
| simpleSumBuggyNotPrivateTest                          | `test/Spec.hs:108` | ns         |         | x     |
| prop_prefixSumIsDifferentiallyPrivate                 | `test/Spec.hs:458` | ps         | x       |       |
| prefixSumBuggyNotPrivateTest                          | `test/Spec.hs:96`  | ps         |         | x     |
| prop_privTreeIsDifferentiallyPrivate                  | `test/Spec.hs:502` | pt         | x       |       |
| prop_privTreeBuggyIsNotDifferentiallyPrivate          | `test/Spec.hs:506` | pt         |         | x     |
| prop_rnmIsDifferentiallyPrivate                       | `test/Spec.hs:435` | rnm        | x       |       |
| prop_rnmBuggyIsNotDifferentiallyPrivate               | `test/Spec.hs:447` | rnm        |         | x     |
| prop_smartSumIsDifferentiallyPrivate                  | `test/Spec.hs:454` | ss         | x       |       |
| prop_smartSumBuggyIsNotDifferentiallyPrivate          | `test/Spec.hs:462` | ss         |         | x     |
| prop_sparseVectorIsDifferentiallyPrivate              | `test/Spec.hs:466` | sv         | x       |       |
| prop_sparseVectorBuggyIsNotDifferentiallyPrivate      | `test/Spec.hs:482` | sv         |         | x     |
| prop_sparseVectorBuggy4IsNotDifferentiallyPrivate     | `test/Spec.hs:490` | sv         |         | x     |
| prop_sparseVectorBuggy5IsNotDifferentiallyPrivate     | `test/Spec.hs:494` | sv         |         | x     |
| prop_sparseVectorBuggy6IsNotDifferentiallyPrivate     | `test/Spec.hs:498` | sv         |         | x     |
| prop_sparseVectorGapIsDifferentiallyPrivate           | `test/Spec.hs:514` | svGap      | x       |       |

#### Claims not supported by this artifact

The statistical tests we perform on the two versions of DAS are not released in
this artifact archive: because 1) these tests require a cluster, lots of disk
space, and the 1940s Census Data to run, and 2) we are not allowed to release
the 1940s Census Data along with this software package.

#### Detailed guide on writing your own program and testing it

*TODO*
