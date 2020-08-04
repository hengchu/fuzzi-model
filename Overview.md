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

We will walk through an example of implementing a simple noisy count algorithm
in FuzzDP. The algorithm can be motivated by the following scenario:

A teacher is grading an exam for a group of students, and also releasing
statistics on the number of students that passed/failed the exam. Suppose there
were 50 students in total, and 49 of them took the exam as scheduled, among
which 39 passed, and 10 failed, and the teacher published the following statistic:

| Pass | Fail |
|------|------|
| 39   | 10   |

The one student who did not take the exam as scheduled took the exam at a later
time. Now, suppose the teacher updates the statistic like the following:

| Pass | Fail |
|------|------|
| 39   | 11   |

Then, just by comparing the published statistics, we can deduce the student had
failed the exam, even though the teacher did not publish any identifiable
information about any student.

A better alternative is to publish these statistics by adding a certain amount
of noise, so that this process is differentially private.

We model this problem using FuzzDP. First, we define the criteria of passing the
exam. Let's say the passing grade is 60/100.
```haskell
passOrFail :: forall real bool.
  ( FuzziType real
  , FracNumeric real
  , CmpResult real ~ bool
  ) => Fuzzi real -> Fuzzi bool
passOrFail score = score %>= 60.0
```

Next, we define a function that counts how many passing scores there
are in an input list of scores, and adds randomly sampled noise to the count.

We need to decide how much noise to add. This step requires some analysis of how
adding/removing a single score from the input may influence the exact count of
number of passing scores. In this case, adding/removing a single score can
change the exact count by up to 1. This factor is known as the "sensitivity" of
a private value.

If a private value has sensitivity `s`, and we add noise sampled from the
laplace distribution with width `w` to it, then the resulting algorithm is
`s/w`-differentially private. In other words, the privacy parameter epsilon for
such a procedure is `s/w`. In this example, we choose the width to be `1.0`, so
that `countPassedDP` is a 1-differential private program. We will use FuzzDP's
testing combinators to check this property.

```haskell
countPassedDP :: forall m real.
    FuzziLang m real => [Fuzzi real] -> Mon m (Fuzzi real)
countPassedDP []     = lap 1.0 0
countPassedDP (x:xs) = do
  ifM (passOrFail x)
      (do
          tailCount <- countPassedDP xs
          return (1.0 + tailCount))
      (countPassedDP xs)
```

These functions have some elaborate type signatures and typeclass
constraints. These constraints enable us generalize the same piece of code for
the two kinds of interpretation that FuzzDP uses: concrete interpretation, and
symbolic interpretation. This flexibility comes at the cost of moderately
complex typeclass based abstractions. More details about these types and
typeclasses can be found in FuzzDP's documentation, which we also provide along
with the docker image. Please see the section below on how to best read the
documentation.
