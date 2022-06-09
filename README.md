# Anosy: Approximated Knowledge Synthesis with Refinement Types for Declassification

This is the artifact for our PLDI 2022 submission, _[Anosy: Approximated Knowledge Synthesis with Refinement Types for Declassification](https://sankhs.com/static/anosy-pldi22.pdf)_.

---
This artifact Docker **does not work** on a M1 Mac machine. You might need to separately install individual components together.
---

## Getting Started

Our artifact uses Docker. Instructions to install Docker can be found [here](https://docs.docker.com/install/).

After Docker is installed, run the following command to build and enter the Docker container that will be used for artifact evaluation. This will download the docker image and install all system dependencies, and drop you inside the artifact image environment.

```
bash setup_docker.sh
```

**Note:** Open Docker Desktop, and go to Preferences > Resources > Advanced and then increase the memory to 6 GB. We have found builds crash when memory is set to 2 GB.

---
Ensure you have the latest version of Docker Desktop (4.5.0 at the time of writing). Sometimes running Docker requires `sudo`. If the above command fails, trying running it again with `sudo`.

If you face errors like below, ensure that you have the Docker Desktop app (or the Docker daemon) running in the background:

```
Cannot connect to the Docker daemon at unix:///var/run/docker.sock. Is the docker daemon running?
```
---

Once inside the Docker container's shell, you should be in the `/root/anosy` directory (assumed to be the working directory from now on). Run the following command to build and install LiquidHaskell:

```
cd ~/liquidhaskell && stack install liquidhaskell
```

Then build the GHC plugin for run the Anosy Synthesizer:

```
cabal update
cd ~/anosy/anosySynth && cabal v2-install --lib --package-env=anosy AnosySynth
```

You could peek around and do some evaluation, after you are done, just `exit` or Ctrl-D to quit. Use the command `docker commit anosy-artifact anosy-artifact-img` to save the state of the container. Next time when you want to start from where you left, just do:

```
docker start -ia anosy-artifact
```

---
**Starting over:** In case the Docker container is broken and you want to destroy your Docker container and start over again run the following command, and then follow instructions from the previous section.

```
docker rm anosy-artifact
docker rmi anosy-artifact-img
```

---

## Basic Testing: Kick the tires phase

Once you are in, you can run some basic benchmarks to ensure everything works. We have a small benchmark suite that runs much faster and can give you a preview of the results.

```
cd ~/anosy
python3 runner.py --smallbench
```

The `Ship` benchmark will be completed for 4 scenarios: interval over-approximation and under-approximation, and powerset of size 3 for both over-approximation and under-approximation. It will create 4 files: `underapprox1.csv`, `underapprox3.csv`, `overapprox1.csv` and `overapprox3.csv`, with the entries for `Ship` benchmark.

These CSV files can be viewed in the artifact's `anosy` folder in the host filesystem.

## File structure in artifact image

Under `~/anosy`:

* `anosySynth/`: Contains the GHC plugin that parses the Haskell source annotation and synthesizes the indistinguishability set and posterior computing functions for a specified approximation. The following briefly includes pointers to the structure of the source in `src/` directory.
  * `Domains/PowerSet.hs`: Defines intervals and powersets types and their typeclasses to lift these data types back to their Haskell source files that are synthesized.
  * `Language/Ghc/Misc.hs`: Utility functions for accessing the GHC AST format.
  * `Language/SMT/ToSMT.hs`: Translates GHC AST to SMT format.
  * `Language/SMT/Constraints.hs`: Defines some auxiliary SMT function definitions that are used in the final SMT output.
  * `Text/SExpression/` and `Text/SExpression/SExpression.hs`: S-Expression parser using the Megaparsec library, that parses output from Z3 in the SMT-LIB format. The parser is a modified version of open-source repository [here](https://github.com/rcook/sexpr-parser).
  * `AnosySynth.hs`: The entrypoint for the GHC plugin (the `install` and `pass` functions). Deserializes the definitions from GHC, generates constraints, and solves them to output a new output file.
  * `LiquidGenerator.hs`: Generates the type definitions needed by LiquidHaskell to verify the generated source file from synthesis phase.
  * `Solver.hs`: Creates the SMT file, solves it and lifts back the result to the PowerSet data type.
  * `Utils.hs`: Some shared utility functions.
  * `Z3Interface.hs`: Interface to the Z3 solver, runs the Z3 binary and parses the output.
* `benchmarks/`: The benchmarks used in the paper used to evaluate Anosy.
* `examples/`: Some working example of benchmarks. Running the evaluation scripts produces outputs in this folder.
  * `declassify/`: An implementation of the `AnosyT` monad, layered on top of the LIO monad. Shows an end to end example of using the monad to declassify the `Birthday` query using synthesized posteriors. The following briefly includes pointers to the structure of the source in `src/` directory.
    * `Anosy.hs`: Defines the `AnosyT` monad and the downgrade function from Figure 2.
    * `Birthday.hs`: The birthday problem from the benchmarks set.
    * `BirthdayGen.hs`: The file containing posterior computing functions synthesized by running AnosySynth.
    * `Declassify.hs`: Contains the `main` function that declassifies the secret using a policy `mypolicy`.
    * `Interval.hs`: Definition and refinement types for the Interval datatype.
    * `PowerSet.hs`: Definition and refinement types for the PowerSet datatype.
    * `SecretDefn.hs`: Contains some type alias and utility functions.

## Full Evaluation: Reproducing the tables and figures from the paper


### Figure 5

Producing Figure 5 requires the benchmarks to be run 11 times. The script `runner.py` runs all the benchmarks as needed: it synthesizes the posteriors, verifies them and then computes their size. To run it execute:

```
cd ~/anosy
python3 runner.py
```

If running the benchmark 11 times is too time consuming, you can pass an additional flag to the above script `-t N` where N is the number of times each benchmark should be run.

**Note:** `N=3` is a good number to get a rough estimate for the performance numbers without running the full suite 11 times each to replicate the exact experiment in the paper.

Running this script will produce these CSV files:

* `underapprox1.csv`: Under-approximation with domain intervals. (Figure 5a left half)
* `overapprox1.csv`: Over-approximation with domain intervals. (Figure 5a right half)
* `underapprox3.csv`: Under-approximation with domain powerset of size 3. (Figure 5b left half)
* `overapprox3.csv`: Over-approximation with domain powerset of size 3. (Figure 5b right half)


These files can be found in the `anosy` folder on the host machine. Claims supported by the results:

* The running times for verification and synthesis will follow the same pattern as the paper.
* Most of the sizes will be same as the paper. Difference can show up in 2 cases:
  - There is a timeout, so the current valid size will be reported by the solver. Note, this size is correct, but might not be the most optimal one. This happens on the `Pizza` benchmark (lines 1079-1081 in the paper).
  - Multiple solutions are possible (see last paragraph of Sec 5.2 in paper), and Z3 might return a different solution for a particular optimization task. This happens in the `Ship` example (Fig 1c can have different rectangle under-approximations of the diamond, while all are correct).
* The key things to verify:
  - The size of under-approximate domains will increase or remain same from interval to powersets, i.e., the sizes of `underapprox1.csv` will be equal or lower than `underapprox3.csv`.
  - The size of over-approximate domains will decrease or remain same from interval to powersets, i.e., the sizes of `overapprox1.csv` will be equal or greater than `overapprox3.csv`.
  - All sizes reported in `underapprox{1,3}.csv` should be equal or lower than ground truth (Table 1) and sizes in `overapprox{1,3}.csv` should be equal or more than ground truth (Table 1).

**Note about falsification:** Since any result from optimization is correct, and can be verified to be correct using LiquidHaskell, the computed data can be falsified only if any of the last 3 points above are not satisfied.

### Figure 6

This runs each benchmark configuration 20 times. To change the number edit the `expt2.sh` to update the `TIMES` variable. Run `expt2.sh` as follows:

```
bash expt2.sh
```

This will produce a file `fig6.pdf`. The file can be found on your local machine in the `anosy` folder. Due to the benchmark using random values every iteration, the graph will not be the exact same as the paper. The general trend to notice will be `# instances` (Y-axis) decreases as the `declassified queries` increase (X-axis). The second trend will be higher `k` values will decrease slower than lower `k` values.

This concludes the reproduction of the results presented in the paper. The following sections demonstrate how to use the tool as described in the paper.

## Synthesizing and Verifying posteriors

To run the synthesizer on any benchmark (called `$FILE` henceforth) individually copy the relevant benchmark from the `~/anosy/benchmarks` folder to `~/anosy/examples` folder. The `examples` folder has the `PowerSet` and `Interval` libraries necessary for the synthesized posteriors to function.

Open `$FILE` and the last line will have something similar to:

```
{-# ANN module ("underapprox", "query", 1 :: Int) #-}
```

This module annotation directs the synthesizer. The first member in the tuple is either "underapprox" or "overapprox". The second member of the tuple is the name of the function for which the posteriors will be synthesized. The final argument is a number that indicates the size of the powersets to use. Note, that 1 is equivalent to using an interval.

To synthesize the indistinguishable sets and the posteriors run the following:

```
cd ~/anosy/examples
ghc -package-env anosy -fplugin=AnosySynth $FILE
```

This will synthesize a file `SecretDefn.hs` that has some auxiliary definitions and a file `($FILE)Gen.hs`. The latter can be inspected to see the synthesized values.

To verify that synthesized posteriors are correct run LiquidHaskell:

```
rm -rf .liquid
liquid ($FILE)Gen.hs
```

This will verify the synthesized posteriors are correct and the implementation of the domains.

## Mechanized Proofs

Running LiquidHaskell verifies the implementation against the refinement type specifications. The refinement types can be seen in the `($FILE)Gen.hs` and `Interval.hs` and `PowerSet.hs`.

The manual proofs for the `sizeLaw` and `subsetLaw` can be found in the functions `sizeLaw` and `subsetRangeProof` in the `Interval.hs` file.

## AnosyT Monad

The `AnosyT` monad enables a programmer to combine the synthesized posteriors to write applications that do safe declassification with a quantitative policy. We combine `AnosyT` monad with `LIO` which enforces non-interference. We write such an example application in the `examples/declassify` folder using the `Birthday` problem from our benchmark suite. The description of files are given in the File Structure section above.

To run the `declassify` example, execute:

```
cd ~/anosy/examples/declassify
cabal v2-run
```

This should build and run the code, which will produce the result of the query under safe declassification.

## Writing your own code

The above section serves as a template to modify and write your own applications using Anosy. The `query` is written in a file as such as `Birthday.hs`. The additional annotation following the secret type (`DateOfBirth` in this example) is given to specify the bounds for the fields in the secret data type.

```
{-# ANN DateOfBirth ([
  ("bday", (0, 364)),
  ("year", (1956, 1992))
  ] :: [(String, (Int, Int))]) #-}
```

The above example says the `bday` field has values ranging from 0 to 364 and the `year` field ranges from 1956 to 1992.

The following annotation starting with `{-# ANN module` serves as a directive to the AnosySynth tool to synthesize the indistinguishibility sets and the functions to compute posteriors.

```
{-# ANN module ("underapprox", "query", 1 :: Int) #-}
```

The first field can be `underapprox` or `overapprox`, followed by the name of the query function (`query` in this example), followed by the number of intervals in the powerset (1 means a single interval, or other `k` means powerset of size `k`).

Running AnosySynth on this example by executing the following command will generate `BirthdayGen.hs`:

```
ghc -package-env anosy -fplugin=AnosySynth Birthday.hs
```

The additional definitions required by the synthesized `BirthdayGen.hs` file are contained in the `Interval.hs` and `PowerSet.hs` files. This gives all the files needed to build an application using Anosy. The synthesized posterior can be verified by running:

```
liquid BirthdayGen.hs
```

The `AnosyT` and `downgrade` definitions in the file `Anosy.hs` can be used in the final end application and compiled using the standard GHC compiler. We have a very simple demo of this in the `Declassify.hs` file where we simply run a declassification of the birthday query using `LIO` as an underlying monad. A programmer can integrate this into their own programs.

In the above example Birthday is just a name, any other file and other definitions can be replaced and the tool should work. In fact, all benchmark programs in the `examples/` directory follow the same structure as `Birthday.hs`.

## Contact

Feel free to file an issue on GitHub or send an email to sankha@cs.umd.edu.
