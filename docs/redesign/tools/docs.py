import sys
new = {
'src/api/frflow/api/FrFlowApi.scala': "FrFlow as a front end sees it. Interpreters: the live one over a project, the in-memory one the front ends test on.",
'src/api/frflow/api/Reading.scala': "What a front end reads: the view, a node's diff since its decision, where a change belongs, the model's fingerprint.",
'src/api/frflow/api/view/Overview.scala': "The counts every view closes with, by concept; derived from the view by `Views.overview`.",
'src/core/frflow/core/analysis/Choice.scala': "How the definition in force is chosen among rivals: the accepted one (Lean), or the first listed (examples, tests).",
'src/core/frflow/core/analysis/Resolved.scala': "A valid theory with its definitions in force, and per node what it uses, calls and relies on.",
'src/core/frflow/core/analysis/Shown.scala': "How the code under a node is shown to meet what is decided: proven, tested or assumed, piece by piece.",
'src/core/frflow/core/code/DataRep.scala': "How Scala builds and takes apart the values of a domain type. A handle on Scala: never compared or printed.",
'src/core/frflow/core/expr/Expr.scala': "An expression of the term language: a simply typed lambda calculus over the vocabulary. Binders are unique.",
'src/core/frflow/core/expr/Lambda.scala': "A function of the IR: its parameters, its body and the body's type.",
'src/core/frflow/core/expr/Value.scala': "A constant of the term language: data reified from a Scala value. Maps and sets keep their iteration order.",
'src/core/frflow/core/name/Label.scala': "What every name of the IR shares: a string inside, a type of its own outside, ordered by its text.",
'src/core/frflow/core/spec/Reliance.scala': "How the nodes above a contract stand to it: relied on, or fixing a word they leave open (`.leftOpenAbove`).",
'src/core/frflow/core/ty/DataType.scala': "A domain type: a case class (a Lean `structure`) or an enum (an `inductive`), as Scala and Lean name it.",
'src/core/frflow/core/vocab/BoundarySig.scala': "A boundary: the operations proven code calls but cannot see, in the trait's order, and the error a call may fail with.",
'src/core/frflow/core/vocab/Define.scala': "A named function of the domain (`val d = define { … }`): a Lean `def`, run as Scala.",
'src/core/frflow/core/vocab/Symbol.scala': "An open term of the domain: a fact of the world or an operation of the system.",
'src/decision/frflow/decision/content/Canonical.scala': "The one printing of a content that is hashed, byte for byte today's `protocol.Canonical`.",
'src/decision/frflow/decision/content/CodeFingerprint.scala': "The hash of a node's governed code: of its tokens and layout (`Tokens`), or of its raw text (`Text`, before).",
'src/decision/frflow/decision/ledger/Ledger.scala': "The developer's decisions, per node, oldest first: an append-only log the review states are a fold of.",
'src/decision/frflow/decision/review/Meaning.scala': "What a node's content means apart from its wording: what a decision binds, and what moves the nodes below.",
'src/decision/frflow/decision/review/Reworded.scala': "Whether only words moved above a decision: its chain recomputed with the reworded nodes' meanings as they were.",
'src/decision/frflow/decision/review/Subject.scala': "A node as decisions see it: its content, its place, its governed code and its checks.",
'src/decision/frflow/decision/rules/Accepting.scala': "Accepting nodes, parents first: chosen or confirmed, rivals rejected, what moved only with them confirmed.",
'src/dsl/frflow/dsl/build/Captures.scala': "The terms a flow's lambda captures, by the names the program gave them, read from its serialized form.",
'src/dsl/frflow/dsl/build/Declarations.scala': "The vocabulary something mentions, by name. A monoid merged by every term, so no registry is needed.",
'src/dsl/frflow/dsl/build/Deferred.scala': "A part of a model, built when elaborated: errors accumulate and declarations merge under `mapN`.",
'src/dsl/frflow/dsl/flow/Boundary.scala': "What proven code calls but cannot see: a trait of operations whose calls are recorded as `Flow.Call`.",
'src/dsl/frflow/dsl/node/Node.scala': "A node as the model writes it. `S` is the statement's case, so fluent methods exist only where they apply.",
'src/dsl/frflow/dsl/term/LeanType.scala': "What a Scala type is in the IR, and the domain types it needs declared.",
'src/dsl/frflow/dsl/term/Once.scala': "A value computed on first use and kept: a define's compiled Scala.",
'src/dsl/frflow/dsl/term/Values.scala': "The values in force where plain code runs, read by `Param.value`. Ambient: the plain-code path's one state.",
'src/eval/frflow/eval/Denote.scala': "The Scala meaning of the term language. Law: Lean proves `e = v` exactly when `Denote(e)` gives `v`.",
'src/eval/frflow/eval/ScalaValue.scala': "A value as Scala holds it at run time. Untyped: the IR's types say what it is.",
'src/eval/frflow/eval/run/Examples.scala': "A node's examples run against its promise, its code, the models and the implementations.",
'src/eval/frflow/eval/run/FlowRun.scala': "A flow run against the bound implementations of its boundaries. Run in `SyncIO` by tests, in `IO` in production.",
'src/eval/frflow/eval/run/SyncFlowRun.scala': "The sequential run. Call arguments are bound as run-time symbols, so no value is reified.",
'src/project/frflow/project/code/Governance.scala': "The files each node governs, today's set exactly.",
'src/project/frflow/project/code/ScalaTokens.scala': "A governed file as its fingerprint reads it: comments removed, lines and indentation kept.",
'src/project/frflow/project/pipeline/Analysis.scala': "The pure state of a project: every phase after elaboration, each computed once, on demand.",
'src/project/frflow/project/port/KeyRing.scala': "The developer's signing key and the project's public keys. An algebra so tests sign with a key made in memory.",
'src/project/frflow/project/program/NodeChecker.scala': "One node's check: Lean steps, each followed by a pure judge that may end the check.",
'src/project/frflow/project/projection/Contents.scala': None,
'src/proof/frflow/proof/layout/Layout.scala': "Where each generated module and each authored proof file lives.",
'src/proof/frflow/proof/lean/lower/Lower.scala': "An expression of the IR as a Lean term: today's `LeanPrinter.expr`, same parentheses and names, on typed values.",
'src/proof/frflow/proof/lean/lower/LowerEnv.scala': "What lowering reads of the knowledge base.",
'src/proof/frflow/proof/lean/lower/LowerProg.scala': "A flow's steps as the lines of a `do` block, as today's `LeanPrinter.block`.",
'src/proof/frflow/proof/obligation/Prop.scala': "The statement of an obligation in the logic of refinement, before any Lean syntax.",
'src/proof/frflow/proof/obligation/Tries.scala': "What is tried of a node, in today's order. One-sided: proven, they show something wrong.",
'src/proof/frflow/proof/verdict/CheckKey.scala': "What a node's check depends on; the node is checked again when it moves.",
'src/runtime/frflow/runtime/ContractViolation.scala': "Thrown by a service after reporting a result that breaks its contract.",
'src/runtime/frflow/runtime/Policy.scala': "How a contract's code is checked where it runs: as the developer chose, else by whether Lean proves it.",
'src/testing/frflow/testing/Draw.scala': "The interpreter of `Gen`: a value drawn at a size from a random stream. Law-tested as a monad.",
'src/testing/frflow/testing/Interleavings.scala': "A concurrent flow run with random pauses, compared with the models' sequential reading.",
'src/testing/frflow/testing/PropertyTests.scala': "Plain code tested against its contract, with cases seeded by the examples. Pure given a seed.",
'src/testing/frflow/testing/TestReport.scala': "What testing a node's code found.",
}
for p,t in new.items():
    if t is None: continue
    L=open(p).read().split('\n')
    i=next(k for k,l in enumerate(L) if l.lstrip().startswith('/**') and '*/' not in l)
    j=i
    while '*/' not in L[j]: j+=1
    ind=L[i][:len(L[i])-len(L[i].lstrip())]
    import textwrap
    line=f"{ind}/** {t} */"
    if len(line)<=120: L[i:j+1]=[line]
    else:
        w=textwrap.wrap(t,width=114-len(ind))
        L[i:j+1]=[f"{ind}/** {w[0]}"]+[f"{ind}  * {x}" for x in w[1:-1]]+[f"{ind}  * {w[-1]} */"] if len(w)>1 else [line]
    open(p,'w').write('\n'.join(L))
