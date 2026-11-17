# Ox's trees in Rocq, and the comparison with the JVM

What is proven of Ox is in `examples/ox/README.md`: the model of its threads, over the executions of its code
(`examples/ox/src/main/scala/ox`, `examples/ox/rocq/Proofs/OxThreads`). This directory holds what that model
is joined to by a test, and what the test runs is joined to the model by a theorem
(`FrFlow/Code/Executed.v`): the events of a run of the machine are an execution of the code.

| Directory | What it is | Checked by |
|---|---|---|
| `Tree/` | Ox 1.1.0 whole: the tree of each TASTy file of its jar, generated. Beside the trees, kept by hand and checked by Rocq against what it computes from them: the concurrency kernel and what it takes from outside (`Kernel.v`, `Surface.v`), what is assumed of each member of the JDK it uses (`Assumed.v`), that Ox's code shares no variable between threads (`Memory.v`), and where the meaning of the trees stops (`Meant.v`). | `frflow.project.rocq.OxSourceSuite` |
| `Client/` | 25 programs written against Ox, as trees; `Runs.v`, which says how one is run; and `Runs1.v` to `Runs4.v`, a lemma for each program, in four files so that Rocq checks them at once: Rocq runs their meaning over Ox's trees, as the programs the model's executions are of, on the machine that writes its run out as an execution (`FrFlow/Code/Frames.v`) and stops where a step would not be one an execution has, and must get what the same program gave on the JVM (`docs/THREADS-MEANING.md`). `executions` says that what such a run does is an execution of the code. | `frflow.project.rocq.OxRunSuite` |

The model of executions reads the files of Ox it speaks of from the same jar with the same reader
(`frflow.dsl.compiled.source`), when it is built.
