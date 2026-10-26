# FrFlow: architecture review and redesign (r43, revision 6)

Measured on branch `claude/kind-bardeen-465vv8` at `3aa8cd7` (since revision 1's `fbea98d` only `README.md` changed).
Appendices next to this file:

- `dependencies.txt`: the measured package and module dependencies, cycles, cross-module use of internals.
- `features.md`: every feature and DSL operation, its concept in the target, its use, keep/merge/drop.
- `planned/`: the planned code, an sbt project of ten modules (372 main files, 6,571 lines; 12 test files, 33
  tests). `cd docs/redesign/planned && sbt compile proof/test decision/test dsl/test project/test evaluation/test runtime/test`
  succeeds offline with `-Werror -Wunused:all -Wnonunit-statement -Wvalue-discard`, and all 33 tests pass:
  - four of crm's generated Lean files printed byte for byte from the Lean AST, with a post and a flow lowered from
    hand-written IR and two obligations (`impl`, `unsat`) lowered from `Prop`;
  - one test per authored-proof rule, and the lemmas' own rule;
  - a design re-parented is reviewed, a claim re-parented is not; a short reason is refused; a gone node's decision
    is reported;
  - `examples` on contracts and on assumptions about an operation, `leftOpenAbove` on contracts only;
  - the `vocabulary` field as auth's ledger records it, for a definition and for a claim;
  - the code where it runs: a result that breaks the post is reported, then thrown; an outside system's adapter
    called from a contract's code is checked on each call, and a wrong result of it (crm's SQL bug in small) is
    reported and thrown; an operation the code calls with neither code nor a binding is reported when wired; an
    assumption is checked again only when a value it reads changed; an example the code answers wrongly gives
    `Returned` with what it returned.

  Bodies are written where they carry the design; 62 `???` in 43 files stand for ports of today's code.
- `tools/budget.py`: the size budgets, measured over `planned/`.

## 1. Summary

### The diagnosis in plain words

FrFlow is a compiler. It reads a model written in a Scala DSL, turns it into trees, checks them, and produces three
outputs: Lean files to prove, Scala functions to run and check at run time, and property tests. Around that sits a
store of the developer's decisions. The code does all of this, but it is not organised as a compiler:

1. There is no intermediate representation that the phases hand to each other. The object a user writes (`Lifted`,
   `Node`) prints itself as Lean and compiles itself to Scala on demand. What a term mentions is learned by printing it.
2. The Lean back end works on strings. Fragments carry `⟦name⟧` placeholders replaced by a regex, the open terms are
   lists of names, and three places parse printed Lean back (types, conjuncts, "doing nothing").
3. `Node` is one class for six kinds: 24 fields, 20 of them optional, edges and source positions inside it, and the
   run-time wrapper (`enforce`) and example runner attached to it. `KnowledgeBase` holds the graph, the vocabulary,
   the run-time wiring, the test settings and the violation reporter.
4. The wire format is in the core (`model` depends on `protocol`), and the ledger's rules take the 31-field wire
   record `SnapNode` as their model of a node. How code is shown correct (proven, tested, assumed) is rebuilt in the
   ledger by parsing prefixes of content strings.
5. Inside `model`, all twelve packages form one dependency cycle; every module's sub-packages form a cycle too.
   `private[frflow]` hides nothing, since every module lives in package `frflow`; `lean` and `check` use about forty
   internals of `model`.
6. Several concepts exist twice or more (a Lean type: `model.types.LeanType` and `lean.LeanType`; a test report:
   `Testing.Report` and `protocol.TestReport`; proven/tested/assumed: five places).
7. The decided content of a node is assembled from raw text: a source excerpt cut by line heuristics (which also holds
   the `idea = …` argument), a regex that strips `.under(...)`, and a fingerprint over the raw text of governed files,
   so a comment edit brings a node back.
8. `IDEA.md` is a second statement of the purpose beside the root: unstructured prose with sections that nodes name,
   decided as a pseudo-node `IDEA`, with `From: Q1, Q2` lines pointing at numbered questions of the agent layer.

### The target in plain words

1. One typed IR, made once by an elaboration phase: `Expr` (terms), `Prog` (flows), `Statement` (what a node says, one
   case per kind), `Edge` (the DAG), `Code` (what is attached to an operation), `Vocabulary`. Plain data, no printing.
2. Phases with a type at each stage: DSL → `Elaborated` → `Valid` → `Resolved` → obligations (`Prop`) → Lean AST
   (`LeanModule`) → text. Each back end (Lean, Scala evaluation, run time, tests) is an interpreter of the same IR.
   The Lean AST says everything generated today; the printer decides nothing.
3. A node is `Node(id, prose, statement)`. Edges, code, positions and checks live in their own tables. There is no
   idea section: the purpose is stated by the root and its parts, and a project's `README.md` is ordinary prose that
   FrFlow neither reads nor tracks.
4. The plain-code path (`p.value`, `d.fn`, `knowledge.service`, `knowledge.run`) has a place in the module graph: the
   values in force are a named ambient scope in `dsl`, the sequential run of flows against implementations is in
   `eval`, the concurrent run and the services in `runtime`.
5. Decisions are their own pure module: a content type with a stated form (`V1` today's, `V2` without source text),
   an append-only ledger, review states as a fold of it, and one rule per command. They read a narrow `Subject` per
   node. Existing ledgers read and verify unchanged.
6. Effects are algebras (`ProjectFiles`, `Lake`, `Git`, `LedgerStore`, `KeyRing`, the API) only where a second
   interpreter, a law suite or a capability restriction pays; the programs over them ask for `Monad`, `Parallel`,
   `Clock`. The core takes no `F`.
7. Each module has its own top package, so `private[core]` is a real boundary, and a build test checks the allowed
   package edges, the absence of cycles and the size budgets.
8. A governed file's fingerprint is over its Scala without comments, lines and indentation kept. A one-time signed
   `confirm --rebind` moves existing decisions to it; until then they keep today's behaviour.
9. The code reads one way throughout: a few patterns (4.10), each written the same way everywhere, one name per
   concept, short definitions, and comments only where the names and types do not say it.

### Recommendation

Rebuild in place, step by step, keeping the DSL's surface syntax so that every example's Lean stays byte-identical
and no decision comes back (section 6, 20 steps). Two steps change example sources, both without moving a decision:
the removal of `IDEA.md` and of `idea = …` (step 12), and the examples' test sources on the new API (step 17). The
choices for the owner are in section 4.8; the recommendations are an initial encoding of terms and flows, two named
ambient scopes (fresh variables while elaborating, values in force while plain code runs), and thirteen modules with
one top package each.

## 2. The current architecture

### 2.1 Modules as they are

| Module | Main lines | What it holds |
|---|---|---|
| `protocol` | 758 | JSON wire types and codecs; also the ledger's domain logic (`Ledger.binding`, `forked`, `alternatives`), content hashing (`Content.hash`), `Walk`, `RunCheck`, `NodeKind`, `IdeaReview` |
| `model` | 5,153 | the DSL, the IR (`Tree`, `Steps`), the Lean printer (`LeanPrinter`, `Types`, `Names`), the evaluator (`Eval`), validation, run-time wiring and enforcement, examples, property and model tests, generators, bytecode and lambda reflection, source macros |
| `lean` | 1,340 | composing Lean files from printed fragments; obligations; reading Lean output; depends on `model`'s test fixtures |
| `ledger` | 975 | decide rules, review states, signing, key and ledger files, reports (`CodeProof`, `Proofs`, `Find`), `Idea`, `IdeaDecision` |
| `check` | 1,233 | workspace, inputs, contents, hashes, snapshot, check runner, verdict judges, lake and git processes |
| `api` | 686 | `FrFlowApi` (16 operations), `LiveApi`, view records (`Overview` 30 fields, `NodeDetails` 19) |
| `cli`, `web`, `agent` | 1,168, 167, 528 | front ends and the agent layer (conversation with numbered questions, `IdeaSources`) |

Tests: 5,176 lines across the modules; the examples' tests 1,226 lines.

### 2.2 Concepts and where each is represented

| Concept | Representations today |
|---|---|
| A domain term | `Param` (a `Term` subclass), `Subst.target`, `Printed.paramObjects/paramRefs`, `Ctx.params` (names), `ParamTerm` (wire), strings in `KnowledgeBase.onOp` |
| A type | `types.LeanType[A]` + `Shape` (model); `Types` (Lean text and Scala text printing); `lean.LeanType` (parsed back from Lean text); `TypeDecl` (both texts); `TypeText` (wire); `LeanType.known` (a global `TrieMap` registry fed by derivation, used to type boundary methods read by reflection) |
| A term / formula | `Term[A]` wrapping `Tree` (binders identified by object identity); `Lifted` (lazy tree + its Lean + its Scala); Lean text with `⟦d⟧` markers; `Content.sources` (source text) |
| A flow | `Flow[A]` (HOAS), `Steps` (first order, with `Steps.Outside` for production steps), Lean `do` text, `Flows.run` (Sync), `Flows.onModels`, `Flows.onModel` |
| A node | `Node` (24 fields), `SnapNode` (31), `Content` (JSON strings), `Reviewed`/`Review` (15), `NodeDetails` (19), `CheckedNode`, `TreeNode`, cli `NodeText` |
| An edge | `Node.declaredParents` (object refs), `Keep(invariant, Option[view], exempt string)`, `Node.replaced`, `Node.scope`; `SnapNode.parents/parts/uses/relies/covers/exempts`; `ledger.Graph.dependents` |
| Code attached | `Implementation(contract: String, factory, files with "last is the model file", wiring: String, proven, flowDef, calls)`, `ModelImpl(start, read, outside: Boolean, …)`, `RunTime`, `CodeProof` (parsed from content prefixes `"tested: "`, `"runs: "`), `Testing.testable`, `Snapshots.tested`, `Overview.contractsTested…` |
| An obligation | `Obligation(name, statement: String, description: String)`, `ObligationText` (wire), `Result`, `NodeCheck` |
| A test result | `Testing.Report/Failed/Covered/Replay` (model) and `TestReport/TestFailure/Covered/Counterexample` (protocol), converted by hand in `check.Tests` |
| A decision | `Decision` (12 fields), the ledger file format, `Decide` (command), `Standing`, `Review`, `IdeaDecision` |
| The purpose | the root node; `IDEA.md` (lead and sections), `Node.ideaSection`, `KnowledgeBase.idea`, `Content` fields `idea`, `ideaSection`, `notModelled`; `Question("Q1", …)` in the agent's conversation |

### 2.3 Data flow, end to end

```
examples/*/src: Scala vals built with the DSL (Node, Param, define, Flow, Boundary)
  │  Lifted builds Tree/Steps lazily by calling lambdas (ThreadLocal `Building`);
  │  the same object prints itself (LeanPrinter) and compiles itself (Eval)
  ▼
model.KnowledgeBase ───────────────► service/run: Wiring, Bindings (ThreadLocal), Node.enforce → production code
  │  problems: Validation (regexes over printed Lean: `∃ \(...: X\)`, inScope over type text)
  ▼
lean.Generate(kb, authored, chosen): Vocabulary, Refinement, Obligations, Evals, Coverage
  │  values are (String, Ctx); calls are `⟦d⟧` resolved by regex; idle reparses types (LeanType.nothing);
  │  restates_i reparses conjuncts (LeanText.conjuncts)
  ▼
check.Analysis(kb, workspace, Inputs): Contents (JSON of strings, source cut by line heuristics, IDEA.md sections),
  CheckHash (over Lean text), Snapshots (SnapNode), CheckRunner → lake → Verdict → NodeCheck → .frflow/checks.json;
  Tests → kb.test (model.Testing, unsafeRunSync for interleavings) → protocol.TestReport → .frflow/tests.json
  ▼
protocol.Snapshot ──► ledger.Annotate(snapshot, ledger): Graph(SnapNode), Standing, Review, Decide, CodeProof, IdeaDecision
  ▼
api.View(Annotated) → Overview, NodeDetails, Tree, Inbox → cli text, web JSON, agent
```

### 2.4 The dependency graph, measured

Details in `dependencies.txt`. The module graph is acyclic (sbt enforces it). Inside the modules:

- `model`'s twelve packages are one strongly connected component. 2-cycles: `frflow ↔ types` (28/2 references),
  `frflow ↔ vocabulary` (22/14), `frflow ↔ term` (16/14), `frflow ↔ testing` (11/14), `boundary ↔ flow` (10/11),
  `node ↔ runtime` (7/4), `kb ↔ runtime` (8/2), `node ↔ example`, `kb ↔ testing`. The root package `frflow` (21 files,
  1,447 lines: `Eval`, `LeanPrinter`, `Steps`, `Testing`, `Trees`, `Types`) is used by and uses every other package.
- `protocol`, `lean`, `ledger`, `check`, `api`, `cli` and `agent` each have their sub-packages in one cycle.
- `model` depends on `protocol` (17 references: `NodeKind`, `RunCheck`, `RunTime`, `Walk`, `tooFew`).
- `private[frflow]` is used 171 times in `model`; since all modules are in package `frflow`, it does not stop `lean`
  and `check` from using `Binder`, `Fn.call`, `Names.*` (14), `Steps.of`, `Tree.Do`, `Types.walk`, `LeanType.ofJava`,
  `n.postFn`, `n.opType`, `.paramObjects`, `.built` and `Testing.*` (about 40 sites, listed in the appendix).
- `api` re-exports `ledger` and `check` types (`api/package.scala`), so the front ends' vocabulary is three modules'.
- `lean` depends on `model`'s test configuration (`compile->compile;test->test`), and the `check` and `lean` suites
  build their knowledge bases from `model`'s test fixtures.

### 2.5 Problems, each with where and why it hurts

The rule ids are those of `.claude/skills/scala-fp` (`references/rules.md`).

**P1. No IR between the front end and the back ends** (wrong owner, missing abstraction; B2, B3).
`vocabulary/Lifted.scala` holds a lazy `build`, `printed` (`LeanPrinter().print`) and `compiled` (`Eval.function`); its
accessors `params`, `body`, `types`, `opaques`, `paramRefs`, `defs`, `paramObjects`, `boundaries`, `errors`,
`commutes` are all read off the printed Lean. `KnowledgeBase.termsOf`, `reads`, `defs`, `types` and `Validation` get
"what a term mentions" from the printer's side effects (`Printed`). Analyses therefore depend on printing; a printer
change can change which terms a node is said to use, hence its decided content.

**P2. The Lean back end is string-typed** (illegal states, leaky layer; D5).
`lean/Vocabulary.scala` `resolve` replaces `⟦name⟧` with a regex; `Ctx` is two lists of names; `Refinement.claim`
returns `(String, Ctx)`; `lean/LeanType.scala` parses printed types back (used by `Obligations.idle` and
`Evals`); `printing/LeanText.conjuncts` cuts printed propositions at `∧` (used by `Refinement.conjunctsOf`);
`KnowledgeBase.inScope` finds type names by regex in Lean type text; `Validation.vocabulary` searches printed bodies
for `∃ (… : X)`. The Lean printer is split between `model` (`LeanPrinter`, `Types`, `Names`, `Boundary.lean`,
`TypeDecl.lean`) and `lean`.

**P3. `Node` is one class for every kind** (D1, D2, D3, D11, B2).
`node/Node.scala:14`: 24 constructor fields, 20 optional or defaulted, a hand-written `copy`. Kind is decided partly
by `kind` and partly by which options are set (`isInvariant = rule.isDefined`, `isFlow` from the operation's shape,
`kb.isStatement` from `modelOf.isEmpty`). Sentinels: `ideaSection = ""`, `file = ""`, `at = -1`. Builders reject
combinations with `require`. Edges are object references inside the node (`declaredParents`, `kept`, `replaced`,
`scope`), deduplicated by `System.identityHashCode`. The phantom `M` types nothing at run time. The same file holds
`checkExamples` (example running), `postFn` (an untyped call convention) and `enforce` (run-time checks, sampling,
assumption caching with an `AtomicReference`, reporting, throwing).

**P4. `KnowledgeBase` is a god object** (D1, B5).
`kb/KnowledgeBase.scala`: 52 members covering the graph (parents, parts, ancestors, ordered), the vocabulary (in
force, provisional, definitions used, reads), code (`implementations`, `implement`, `implementProven`, `calledBy`),
running (`service`, `run`, `definitionBindings`, `opCode`, `runtimeAssumptions`), testing (`generators`, `testing`,
`test`), examples, validation and a violation reporter (`onViolation`). Every `with…` rebuilds it by positional
constructor call.

**P5. The core depends on the wire format, and the wire format holds domain logic** (B3, M1, T9).
`model → protocol`; `protocol.decision.Ledger` contains the decision log's semantics; `protocol.Content` the hashing
rule; `RunTime.describe` and `RunCheck.describe` display text (V5). Changing a JSON field touches the core.

**P6. The ledger's model of a node is the 31-field wire record** (V2, V3, D3).
`ledger/review/Graph.scala`, `Standing.scala`, `Meaning.scala` and `Decide.scala` take `SnapNode`. `Meaning.own`
removes `.under(...)` from the `definition` text with a regex. `ledger/report/CodeProof.scala` decides proven, tested
or assumed by looking for the prefixes `"tested: "`, `"assumed, checked: "` and `"runs: "` in content strings.

**P7. Package cycles everywhere, and visibility that does not bound modules** (M1, M4; see 2.4).

**P8. Duplicate representations of one concept** (D3; see 2.2): two `LeanType`s, two test reports with a hand
conversion, five places deciding proven/tested/assumed, `Walk` in `protocol` used by `model`, the name clashes
`Term` (model, `api.details`), `Tree`/`Trees` (model, `api.report`), `Eval` (model, `lean.obligation`), `Words`
(protocol, `cli.text`), `Coverage` (model, `lean`).

**P9. Untyped core with casts** (D11).
133 `asInstanceOf` in `model`; the IR passes `Any`; `Fn.call` dispatches on arity up to nine; `Keep.brokenBy`, `postFn`,
`Wiring.service` cast the results of the developer's functions. A literal is `Tree.Lit(v: Any, …)`.

**P10. Ambient and global state in the core** (E1, E5, E6, E7).
ThreadLocals `Bindings` (values in force, also read by the evaluator), `Watch` (coverage), `Building`; the global
`LeanType.known` registry (types of boundary methods depend on which derivations ran before); `unsafeRunSync` in
`example/ExampleRuns.scala:54`; `sys.env.get("FRFLOW_SEED")` in `check/Tests.scala:34`; reflection on bytecode for
equality (`types/Adt.ownEquality`), on lambdas for parameter names and captured values, on Java generic signatures
for boundary types.

**P11. The decided content is assembled from raw text** (D5, D6).
`check/analysis/Contents.scala`: a JSON object of strings; `definition` is the node's statement cut out of its file by
indentation heuristics (`Contents.definition`), so it holds every argument written there, `idea = "…"` included;
`uses` holds Scala type text from `Types.scala` and define sources; `model` holds Lean text of the boundary model; a
flow's `implementation` holds its Lean. `check/Inputs.scala:56-72` fingerprints the raw text of every governed file
and implementation source, so removing a phrase from a doc comment in
`examples/auth/src/main/scala/auth/SessionStore.scala` put `DecisionContract` back for review (`code`).
`governs: List[String]` paths are resolved only when the checker reads the disk, and `Implementation.files` relies
on the convention that its last element is the model file (`dropRight(1)`).

**P12. Views are flattened copies** (V1, V2, V3).
`SnapNode` (31 fields), `Overview` (30 counters, 9 defaulted), `NodeDetails` (19), `Review` (15). Each is built field
by field; `Overview.of` repeats knowledge (`CodeProof`, `provenDown`) found elsewhere.

**P13. Errors are thrown from the model** (F8, F9, R1).
`require` in builders, `IllegalArgumentException` from the printer (`cannot infer the type here`), from `Types`
(function fields, redefined equality), from `Steps` (transaction inside a transaction). A model error surfaces as a
stack trace while the model loads or while Lean is printed, one at a time.

**P14. Effects are not separated into algebras** (A1, A2, X4).
`check.Disk`, `Lake`, `Git`, `JsonStore`, `KeyStore` are concrete `IO` objects; the checker's tests need Lean installed
or rebuild the workspace on disk. `LiveApi` is the only interpreter of `FrFlowApi`.

**P15. The DSL's surface is wider than its users** (S1).
`features.md`: `race`, `guarantee`, `bracket`, `timeout`, `parTupled`, `ifM`, `checkedAtRunTime`, `testedWith`,
`reporting` have no use in the examples; `Boundary[T] => T` is an implicit conversion hiding an access (T6).

**P16. Behaviour is pinned only on fixtures.** `lean/GoldenSuite.scala` pins the generated Lean of two fixtures;
nothing pins the examples' Lean, contents, signatures or snapshots, which is what a refactoring must preserve.

**P17. Two statements of the purpose** (D3; the owner's call). The root says what the system is for, and so does
`IDEA.md`, as prose with sections. Nodes name sections (`idea = "…"`), contents carry the section's text, an `IDEA`
pseudo-node is decided and reviewed by section, and the agent layer links sections to questions numbered `Q1`, `Q2`
(`IdeaSources`), a numbering defined nowhere a reader of the files can see. Its own files are 98 lines
(`Idea`, `IdeaDecision`, `IdeaReview`, `IdeaSources`), plus branches in `model`, `check`, `api`, `cli` and `agent`.

## 3. Sources, and what this design takes from each

- **Compiler phases with typed intermediate representations.** Sarkar, Waddell and Dybvig, "A nanopass infrastructure
  for compiler education", ICFP 2004 ([program](https://icfpconference.org/archived/icfp2004/www.cs.indiana.edu/icfp04/program.html)),
  and the journal version, JFP 15(5) 2005 ([pdf](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1E378B9B451270AF6A155FA0C21C04A3/S0956796805005605a.pdf/educational-pearl-a-nanopass-framework-for-compiler-education.pdf));
  Keep and Dybvig, "A nanopass framework for commercial compiler development", ICFP 2013, which rebuilt Chez Scheme
  this way. Taken: many small passes, each with a declared input and output language. FrFlow gets a type per stage
  (`Elaborated`, `Valid`, `Resolved`, `NodeObligations`, `LeanModule`) and one pass per change of representation.
- **Scala 3's compiler** is a list of phases over typed trees ([overall structure](https://nightly.scala-lang.org/docs/internals/overall-structure.html));
  Petrashko, Lhoták and Odersky, "Miniphases", PLDI 2017 ([paper](https://plg.uwaterloo.ca/~olhotak/pubs/pldi17b.pdf)).
  Taken: trees whose nodes carry their types (`Exprs.typeOf` is total), so passes need no environment to type a
  subterm.
- **Front end, IR, back ends.** Nystrom, *Crafting Interpreters* (2021): a front end to a tree, and several walkers of
  the same tree (resolver, interpreter). Taken: Lean lowering, Scala denotation, run-time checking and test generation
  are four interpreters of one IR; the Lean printer is a last, decision-free walk over a Lean tree.
- **Extensible trees.** Najd and Peyton Jones, "Trees that grow", JUCS 23 (2017) ([paper](https://arxiv.org/pdf/1610.04799)):
  one AST indexed by phase. Considered and not taken: FrFlow's stages differ in what surrounds the trees (choices,
  derived relations) more than in the trees, so separate stage types around one `Expr` are simpler.
- **DSL encodings.** Carette, Kiselyov and Shan, "Finally tagless, partially evaluated", JFP 19(5) 2009
  ([Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/finally-tagless-partially-evaluated-tagless-staged-interpreters-for-simpler-typed-languages/7B2DC44A2127EBBA71ADE63809D9425F)).
  Weighed in 4.8; FrFlow inspects, rewrites and hashes its terms, which favours the initial encoding.
- **Higher-order syntax without names clashing.** Axelsson and Claessen, "Using circular programs for higher-order
  syntax", ICFP 2013: binders numbered from the body. Weighed in 4.8 against an ambient supply.
- **Algebraic design.** Chiusano and Bjarnason, *Functional Programming in Scala* (2014; 2nd ed. 2023), ch. 7–9:
  write the operations and laws first. Taken for `Gen` (a lawful `Monad`), `Declarations`, `Notes`, `Mentions`,
  `Hits`, `Tally` (monoids), `Deferred` (an applicative), the algebras of the shell with law suites.
- **Functional core, imperative shell.** Bernhardt, *Destroy All Software* ([screencast](https://www.destroyallsoftware.com/screencasts/catalog/functional-core-imperative-shell))
  and "Boundaries" (2012). **Ports and adapters**: Cockburn (2005); Seemann, "Functional architecture is Ports and
  Adapters" ([blog](https://blog.ploeh.dk/2016/03/18/functional-architecture-is-ports-and-adapters/)). Taken: every
  phase is pure; `project.program` reads inputs once through algebras, calls the phases, writes results.
- **Information hiding and deep modules.** Parnas, "On the criteria to be used in decomposing systems into modules",
  CACM 15(12), 1972 ([text](https://www.cse.sc.edu/~mgv/csce330f24/ParnasCriteria.pdf)); Ousterhout, *A Philosophy of
  Software Design* (2018). Taken: each module hides one design decision (how Lean is spelled; how Scala holds values;
  how decisions are stored) behind a small interface; the decision rules see a `Subject`, never the IR or Lean.
- **Simple made easy.** Hickey, Strange Loop 2011 ([talk](https://thestrangeloop.com/2011/simple-made-easy.html)):
  do not complect. Taken: a node's statement, its edges, its code, its position and its checks are five facts stored
  apart, each once; the purpose is stated once, by the root.
- **Types for the domain.** Wlaschin, *Domain Modeling Made Functional* (2018): make illegal states unrepresentable,
  model stages as types. Taken: `Statement`'s cases (a contract on a function and one on a flow are two cases), the
  two example shapes, `Valid` as an opaque type only `Validate` makes, `RelPath` only `parse` makes.
- **Event sourcing.** Fowler, "Event Sourcing" ([martinfowler.com/eaaDev/EventSourcing.html](https://martinfowler.com/eaaDev/EventSourcing.html));
  Young, CQRS and event sourcing ([talk transcript](https://kurrent.io/blog/transcript-of-greg-youngs-talk-at-code-on-the-beach-2014-cqrs-and-event-sourcing)).
  Taken: review states are a fold of the log over the current graph (`Standings.of`); commands (`Decide`) produce
  events (`Decision`s) or refusals; an event's schema changes by versioning it (`Format`), never by rewriting the log.
- **Typelevel practice.** cats, cats-effect and discipline documentation; Volpe, *Practical FP in Scala*: algebras as
  `trait X[F[_]]`, interpreters built by `make` as `Resource`s, programs with the least capability, law suites
  against every interpreter. Taken where a second interpreter or a law exists (4.7).
- **Checking architecture in the build.** ArchUnit ([user guide](https://archunit.org/userguide/html/000_Index.html))
  is for Java bytecode; `layers-dotty-plugin` (Scala 3, version 0.0.x) and `sbt-dependency-rules-plugin` (classpath
  only) exist. Section 7 uses a small import scanner as a munit test instead, plus scalafix's built-in
  `DisableSyntax`.

## 4. The target architecture

### 4.1 Concepts, each with its theory

1. **Vocabulary** (`core.vocab`). The signature a model is written over: sorts (opaque types), declared data types,
   symbols (open terms), defines (named functions with bodies), boundaries (operation signatures) and state models.
   Law: each name is declared once (`Validate` reports `DeclaredTwice`). A symbol is an operation exactly when a
   promise is about it; that is derived, not stored. Elaboration collects the vocabulary from what the terms declare
   (`dsl.build.Declarations`, a monoid that keeps two different declarations of one name for `Validate` to report),
   with no registry.
2. **Expr** (`core.expr`). A simply typed lambda calculus with data, containers and quantifiers. Every node carries
   what its type needs (`Exprs.typeOf` is total); binders have unique ids (`VarId`). One operator per meaning: an
   operator on several containers (`Contains` of a list, an option or a set) is one `PrimOp`, its operand's type
   telling which; every operation with a body (`forall`, `exists`, `filter`, `find`, `map`, `flatMap`) is
   `Expr.Iterate` with a binder, a fold `Expr.Fold`. Two meanings, Lean's (`proof.lean.lower.Lower`) and Scala's
   (`eval.Denote`), which agree on every closed computable expression; the examples' and probes' evaluation in Lean is
   the cross-check (`Prop.Evaluates`). `Mentions` (a monoid) says what an expression mentions, binder types included.
3. **Prog** (`core.expr`). A proven flow's steps, first order: the free monad over the boundaries' operations and the
   models' state, with errors and loops. Meanings: a Lean `do` block, a run on the models, a run against
   implementations (`eval.run.FlowInterpreter`). Concurrent steps hold their branches and binders
   (`Par(left, leftResult, right, rightResult)`); their sequential reading is derived (`Progs.sequential`). There is
   no outside step: production steps live in the DSL's `Flow` only.
4. **Statement and Node** (`core.spec`). `Node(id, prose, statement)`; `Statement` has one case per kind (`Claim`,
   `Invariant`, `Contract` on a function, `FlowContract` on a flow with its `FailureClause`, `Fact`, `AssumedCall`,
   `Model`, `Definition`, `Design`), each with only its data. A function's examples are `CallExample(inputs, result)`;
   a flow's are `RunExample(inputs, before, end)`. `kind`, `operation` and `exprs` are functions of the case.
5. **Refinement** (`core.graph`). The DAG: nodes in the model's order and `Edge`s (`PartOf`, `Replaces`, `Keeps`,
   `Exempt`). Laws, made true by `Validate`: one root (a claim or invariant without parents), acyclic, every edge
   inside the graph.
6. **Scope** (`core.analysis.Scope`). The nodes an invariant applies to: within the nodes it names as scope, the
   contracts whose result can hold what its rule is about (a type holds it when it names it, or a type whose fields
   hold it, read off `Ty` and `DataType.fieldTypes`), and the designs governing code no proof below the rule covers.
   `Validate` asks each of them to keep the invariant or be exempt. Today's `inScope` regex over Lean type text, on
   types.
7. **Code** (`core.code`). What is attached to an operation (`Proven`, `ProvenBeside`, `ProvenFlow`, `Tested`), at most
   one per node (`CodeTable.attached: Map[NodeId, Attachment]`), and the implementations run against a model
   (`CodeTable.realized`, `Outside` or `Own`). How each piece of code is shown is one function, `Shown.of`:
   `Shown(proven, tested, assumed)`, a list per kind, so production code beside a proven define is proven and tested,
   and a model with both kinds of realization is described piece by piece.
8. **Resolution** (`core.analysis`). `Validate` makes a `Valid` model or returns every `Problem`; `Resolve` picks the
   definitions in force (`Choice.Decided` for Lean, `Choice.FirstListed` for examples, tests and services) and
   computes once what each node uses, calls and rests on. Every later phase reads `Resolved`, which only `Resolve`
   makes.
9. **Obligation** (`proof.obligation`, `proof.terms`). What Lean is asked of a node, as a proposition in the logic of
   refinement: claims, conjuncts and expectations stand applied to their open terms (`ClaimOf(n, σ)` with operations
   replaced by code or by nothing), `Implies` with named hypotheses, `Iff`, `Both`, `Not`, `False`, evaluations,
   commutation, and `Forall(about, body)`/`Exists` that bind the open terms of the claims of the nodes it is about,
   then of its conclusion, then of its hypotheses. `TermTable` (computed once per analysis, each define's terms once)
   says what each declaration is applied to: its open terms in order (a flow contract's claim with its failure
   clause's), each symbol's type, what the definitions in force fix terms as. The required set and the tries are
   today's, in today's order, each made with the sentence its Lean is documented with.
10. **Lean** (`proof.lean`, `proof.layout`, `proof.reading`, `proof.verdict`). A Lean AST able to say everything
    generated today; `lean.lower` gives each `Expr` and `Prog` its Lean term, naming variables in `State[Naming, _]`
    and placing every parenthesis, each `Prop` its statement (`LowerProp`, a `Writer` of the open terms met) and each
    obligation its declaration (`LowerObligation`); `Print` is a fold that decides nothing;
    the proof-file rules and the judges are pure functions returning cases.
11. **Decision** (`decision`). `Content` (named fields of three shapes, a canonical print, `hash` and `ref`) with its
    form (`Format.V1`, `V2`) read off the fields; `Chain`; `CodeFingerprint` (`Text` or `Tokens`); `Decision`;
    `Ledger` (append-only, laws on `add` and `history`); `Payload` and `Seals` (signing, pure once the keys are read);
    `Standings` (the fold, with rewording); `Decide(reading, command, author)` (one rule per `Command`). It reads
    `Subject`s only.
12. **Shell** (`project`, `api`, `wire`). Algebras over `F[_]` where they pay (4.7), programs over them, the `Analysis`
    value (every pure phase computed once from the inputs), the API whose views are functions of a derived `View`,
    and the export formats.

The plain-code path, the part of FrFlow a production system links against, uses concepts 1–4 and 7 and four pieces
of state, each named (4.8.B): `dsl.build.Fresh`, `dsl.term.Values`, a define's compiled Scala (`Def.compiled`), and
the knowledge base's elaborated model (`KnowledgeBase.elaborated`, a `lazy val` of an immutable value); a running
service adds the watch's cell and the samplers' counters (`runtime.check`).

### 4.2 Phases and their types

| Phase | From | To | Module | Effects |
|---|---|---|---|---|
| construct (the user's vals) | Scala | `dsl.node.Node[S, F]` (head + `Deferred[S]`), `Term`, `Flow`, `Def`, `KnowledgeBase` | `dsl` | none; nothing runs |
| elaborate | `KnowledgeBase` | `ValidatedNec[ElabError, Elaborated]` | `dsl.kb.Elaborate` | calls the user's lambdas once; `Fresh` ambient for its duration |
| validate | `Elaborated` | `ValidatedNec[Problem, Valid]` | `core.analysis.Validate` | pure |
| resolve | `Valid`, `Choice` | `Resolved` | `core.analysis.Resolve` | pure |
| evaluate | `Resolved` (first listed), `Denote` | `Computed`: example results, `Evaluation`s | `project.program.Evaluate` over `eval.run.Examples` | `F: Sync` (the developer's code runs) |
| obligations | `Resolved` (decided), authored set, evaluations | `List[NodeObligations]` | `proof.obligation.Obligations` | pure |
| lower and lay out | `Resolved`, obligations, `TermTable` | `List[LeanModule]` | `proof.lean`, `proof.layout.LeanProject` | pure |
| print | `LeanModule` | `String` | `proof.lean.print.Print` | pure |
| prove | modules | `ProverRun`s → `Judged` → `NodeCheck` | `project.program.NodeChecker` over `Lake` | `F` |
| test | `Resolved`, `Denote`, `Plan` | `Option[TestReport]` | `testing.PropertyTests`, `Interleavings` | pure given a seed; `Interleavings` needs `Async` |
| run | `Elaborated`, `Reporter` | services (plain functions); a flow's run in `F` | `runtime` over `eval.run.FlowRun` | synchronous wrapper; `F: Sync` |
| project | `Resolved`, checks, sources | `Content` per node (`V2`), `Subjects` | `project.pipeline.Contents`, `ReadSubjects` | pure |
| review | `Subjects`, `Ledger` | `Map[NodeId, Standing]` | `decision.review.Standings` | pure |
| decide | `Reading`, `Command`, `Authorship` | `Either[Refusal, Ledger]` | `decision.rules.Decide` | pure; signed and stored by `DecideProgram` |
| export | `Analysis` | `wire.snapshot.Snapshot`, `checks.json`, `tests.json`, ledger file | `wire` | codecs only |
| view | `Analysis`, warnings | `View`; `Views.overview/beside/tree/inbox` | `api.view`, `api.node` | pure |

`project.pipeline.Analysis(valid, inputs, computed)` holds the stages after validation as lazy values (`decided`,
`provisional`, `obligations`, `modules`, `subjects`, `standings`), so an operation computes only what it reads and each
stage once. It holds the model once (`Valid` wraps the `Elaborated`).

### 4.3 Modules and the direction of dependencies

```
   core ◄── dsl ◄── eval ◄── testing
    ▲  ▲             ▲  ▲
    │  └── proof     │  └── runtime  (facade `frflow.*`: the DSL, `d.fn`, `service`, `run`)
    └───── decision  │
   wire ─► proof, decision, testing (the export formats)
   project ─► proof, testing, decision, wire        (the shell: algebras, programs, analysis)
   api ─► project ;  cli, web ─► api ;  agent ─► cli, web
```

| Module | Top package | Depends on | Holds |
|---|---|---|---|
| `core` | `frflow.core` | cats-core | names, `Ty`, `Expr`, `Prog`, `Value`, vocabulary, statements, examples, `Gen` (data), edges, code, `Theory`, `Elaborated`, `analysis` |
| `dsl` | `frflow.dsl` | core | the surface syntax and elaboration (`build`, `term`, `shape`, `node`, `flow`, `kb`); `Values`, `Once`; source and derivation macros |
| `proof` | `frflow.proof` | core | obligations, open terms, Lean AST, lowering of terms and statements, printing, layout, proof-file rules and Lean's output, judges |
| `eval` | `frflow.eval` | dsl, cats-effect-kernel, cats-effect-std | `Denote`, `Env`, `Literals`/`Reflect`, `Fn` (casts), `DefSyntax` (`d.fn`), `run`: `FlowInterpreter` with `FlowRun.sequential` and `FlowRun.concurrent`, `Examples`, `Probes` |
| `testing` | `frflow.testing` | eval | `Draw`, `Shrink`, `Hits`, `Position`, property and model tests, `Interleavings` (over `FlowRun.concurrent`) |
| `runtime` | `frflow.runtime`, `frflow.runtime.check` (+ the facade `frflow`) | eval, cats-effect | `Running`, `Service`, `Guard`, `Policy`, `Wiring`, `Violation`, `Reporter`, `RunSyntax`; `check.CallValues`, `AssumptionWatch`, `Sampling` |
| `decision` | `frflow.decision` | core (names, `graph.Walk` only) | content, ledger, signing payload, review, rules |
| `wire` | `frflow.wire` | proof, decision, testing, circe | the snapshot by kind (planned: its types); the codecs of the ledger file, checks and tests |
| `project` | `frflow.project` | proof, testing, decision, wire, cats-effect, fs2 | algebras and interpreters, programs, `Analysis`, contents and subjects, code fingerprints, configuration |
| `api` | `frflow.api` | project | `Reading`, `Deciding`, `Proving`, `FrFlowApi`, the view (`api.view`) and the node views (`api.node`) |
| `cli`, `web`, `agent` | `frflow.cli`, `frflow.web`, `frflow.agent` | api (agent: also cli, web) | front ends and the agent layer |

Thirteen modules. The planned code has the first ten; `cli`, `web` and `agent` keep their structure and are rebuilt on
the new API (step 17).

**The plain-code path through the graph.** `eval` depends on `dsl`, so everything that runs the developer's code sits
above both the values in force and the define handles:

- `Param.value` is in `dsl.term.Param` and reads `dsl.term.Values` (a `ThreadLocal` map, set for one call by
  `Values.within`). Reading it while a term is being built is a `Fault.ValueReadWhileBuilding`.
- `d.fn` is `eval.DefSyntax` (an extension exported by the facade): it compiles the define's elaborated lambda with
  `Denote` on first use and keeps the function in `Def.compiled: Once[AnyRef]`.
- `eval.run.Examples` and `testing.PropertyTests` run attached plain code under the examples' givens and the generated
  worlds with `Values.within`; `runtime.Service` does the same per service call.
- `eval.run.FlowInterpreter` is the one interpreter of flows: a proven flow's `Prog`, and the DSL `Flow`s an
  implementation's operations return, `Effect` steps included. A call's arguments are passed to the implementation as
  run-time symbols bound in the `Env` (`$argN`), typed by the operation's `OpSig`; every flow the developer's code
  builds (the operation's, and each continuation's) is built in a `Fresh` scope of its own, so a term with a binder
  (`xs.filter(…)`) built at run time is legal. A failure is a
  `FlowError` raised in `F`. `FlowRun.sequential[F: Sync]` runs concurrent steps in turn (`Parallel.identity`);
  `FlowRun.concurrent[F: Async](…, pause)` runs them on fibers with `atomically` under one `Mutex`, `pause` before
  every call. `testing.Interleavings` uses the second with random pauses; `knowledge.run[F]` the first, as today.

**The code where it runs, one job per function.** Today's `Node.enforce` and `Node.checkExamples` are each one long
extension method doing everything. Here each job is a small named function, and the two share the call check:

- `eval.run.CallCheck.of(denote, theory, node)`: what one call is checked against, compiled once: the post, the check
  run time uses (`checkedBy` when given, else the post, with the `Broken` it reports), the invariants the contract
  keeps (`Kept`, each through its view); `broken(call, env): Option[Broken]`.
- `eval.run.Givens` (today's `Examples.env`): an example's givens as values in force (`values`, for `Values.within`)
  and as the symbols of an `Env` (`env`); data and tables are literals of the symbol's type, code runs when read.
- `eval.run.PromiseExamples`: each call example against the promise: a fact its givens break (`Assumes`), else the
  post's answer against the verdict, and an accepted `expect` checked against the kept invariants.
- `eval.run.CodeExamples` (today's `checkExamples` on code): the code built once per set of givens (a `Try`, kept in a
  fold), called through `Fn.call` under `Values.within`, and judged: an invariant broken (`Breaks`), the result
  against the example's (`Agrees`), else `Returned(value)`; a throw is `Breaks(Threw(message))`.
- `runtime.Wiring.values`: what is wired (the bindings given, the other operations' services) over the definitions
  in force (the first listed, each computed by its term when read, `Applied.called`). What must be bound is today's
  `needed`: what the promise reads, what its examples give values to, and what its code calls (plain code's calls
  as attached, a define's mentions); one bound by none is `WiringError.Unbound`, when wired.
- `runtime.Running.wired`: the attachment, the code (an `Impl`; a proven define through `Denote.impl`), the
  `CallCheck`, the values, an `AssumptionWatch` over the facts that read only symbols bound (checked once now, else
  `AssumptionBroken`) and the sampler (`Sampling.of(Policy.of(attached))`): a `Service`. Every other operation a
  plain call reaches and whose node has code is its service, wired when first called, as today's `opBindings`: a
  contract's code, and the adapter on an assumption about an outside system's operation (crm's `fetch` on
  `recordsByQuery`, keycloak's `lookup` on `sessionLookup`), so an adapter is checked on each of its calls.
- `runtime.Service.call` (today's `enforce`): a `CallValues` for the call, then under `Values.within` the code built
  and called (`Fn.call`), `Guard.result` (the call check, on the calls sampled), `Guard.values` (the watch), and
  `fail` (report, then throw `ContractViolation`). `Service.as[F]` gives the typed function (`Fn.of`).

State, each piece named and confined. The running system's shared mutable state is two kinds, both in
`runtime.check`: the watch's cell, `AssumptionWatch.held` (an `AtomicReference[Map[NodeId, List[Any]]]`, values
compared by reference, as today), and the samplers' counters, inside `Sampling.of` (today's `chooser`: an
`AtomicLong`, or a seeded `SplittableRandom` used under its lock), each shared by one service's calls. A call's
values, one `Once` each in `CallValues`, are made for the call and dropped after it. The casts are `Fn.call` and
`Fn.of`.

Serialization points outward: `wire` depends on the domain and nothing but the shell depends on `wire`. The front
ends see `api.view` and `api.node` values only. Production code depends on `runtime` (and through it `eval`, `dsl`,
`core`) and never on Lean, the ledger or the CLI.

### 4.4 How a node is represented

Planned code: `src/core/frflow/core/spec/`, `example/`, `code/`; the DSL surface in `src/dsl/frflow/dsl/node/` and
`shape/`. Every field of today's `Node` has a place:

| Today (`node/Node.scala`) | Target | Rule |
|---|---|---|
| `id` | `spec.Node.id: NodeId` | |
| `statement`, `why` | `Node.prose: Prose` | |
| `kind` | the `Statement` case; `Statement.kind` | D1, D3 |
| `declaredParents` | `Edge.PartOf` in `Theory.edges` | edges in the graph |
| `formula` | `Claim.formula`, `Fact.formula: Written[Expr]` | |
| `post`, `local` | `Promise.post`, `Promise.check: Option[Written[Lambda]]` | |
| `op` | `Contract.op`, `FlowContract.op`, `AssumedCall.op: SymbolName` | typed name |
| `rule`, `scope` | `Invariant.rule`, `Invariant.scope: List[NodeId]` | |
| `substs` | `Definition.fixes: NonEmptyList[Fixing]` | D10 |
| `cases` | `Promise[CallExample]` or `Promise[RunExample]` (values reified to `Value`) | D2, D11 |
| `governs: List[String]` | `Design.governs: NonEmptyList[RelPath]` | D4, D6 |
| `kept` (`Keep` with `Option` view and string) | `Edge.Keeps(contract, invariant, view)`, `Edge.Exempt(node, invariant, because)` | D1 |
| `ideaSection = ""` | deleted (P17) | |
| `file = ""`, `at = -1` | `Sited(node, at: Span)` in `Theory.nodes` | D5 |
| `expected` | `Claim.expects: List[Expectation]` | |
| `replaced` | `Edge.Replaces` | |
| `modelOf` | `Statement.Model(model)`; the boundary in `Vocabulary`; realizations in `CodeTable.realized` | B2 |
| `runCheck` | `code.Attachment.runCheck` | B5 |
| `openAbove: Boolean` | `Contract.reliance`, `FlowContract.reliance: Reliance` | D8 |
| `failure` | `FlowContract.failure: Option[FailureClause]` | D1, D2 |
| `[M]` | type parameters on the DSL's `Node[S, F]` only: `S` the statement's case, `F` the operation's type | S2 |
| `parents`, `isInvariant`, `shownKind`, `isFlow`, `opType`, `defines`, `referenced` | `Refinement.parents`, the case, the CLI's renderer, the case, `Ty` of the operation, the case's fixes, `Exprs.mentions` | D3, V5 |
| `under`, `replaces`, `exempt`, `keeps`, `examples`, `checkedBy`, `leftOpenAbove`, `failsChangingNothing`, `onFailure`, `expects` | `NodeSyntax` extensions on `Node[S, F]`; `examples` written once over `OnPromise[S]` (the `AssumedCall` instance in its companion, which also derives one from every `OnContract`), `leftOpenAbove` over `OnContract[S]` (the `Contract` and `FlowContract` instances in its companion); each instance's `withExamples` is `Promise.withExamples` | S2 |
| `checkExamples`, `postFn`, `broken` | `eval.run.Examples` over `CallCheck`, `Givens`, `PromiseExamples`, `CodeExamples` | B2 |
| `enforce` | `runtime.Service` (`Guard`: `CallCheck`, `AssumptionWatch`, `Sampling`; `fail`), wired by `Running.wired` and `Wiring.values` | B2, F1 |

The surface is not a mirror of the core: a DSL node is `Node[S, F](head: Head, statement: Deferred[S])`, the head
holding what every node has as written (id, prose, position, links), and the statement built when elaborated.
`Node.contract(op)(…)(post)` makes a `Node[s.Made, F]` from the operation's `CallShape[F]` (the lambdas over a call,
and the statement a contract on it makes), so a contract on a flow is a `FlowContract` by its type.
`define { (a: Term[A]) => … }` makes a `Def[A => R]` named as its val (`Source.valName`, read at compile time) from the
define's `DefineShape[F]` (a lambda over the inputs only, making no statement). A lambda's parameter names come from
its tree at compile time (`Source.of`), not from reflection.

**An error waiting for its place.** The front end has one shape for a part of a model built later, `Deferred[A]`
(errors accumulate, declarations merge), and one for an error found before its place is known: a `Fault` (an enum
with no site). Terms carry faults (`Notes.faults`), constants that are not data give one (`Reify`, `Lift`), and a
lambda that cannot return a term throws a `Failure(fault)`. `Elab` places them once at the part's `Site` (a node, or
a define): `ElabError(at: Site, fault: Fault)`.

### 4.5 Views are derived, and the API

- `api.view.View(nodes: List[NodeView], root, overview, warnings)` is derived once from the analysis (`Views.of`);
  the front ends see it and never `Analysis`.
- `api.node.NodeView(id, says, place, proof, code, review)` replaces `NodeDetails` (19 fields) and the view's half of
  `SnapNode` (31), one group per concept, each made by one function of `api.node.NodeViews`:

| Group | Fields | Replaces |
|---|---|---|
| `Says` | `kind`, `statement`, `why`, `written` (the formal parts as written), `mentions` | `node`'s texts, `terms`, `defs` |
| `Placement` | `root`, `related: List[(Relation, NodeId)]`, `apply(relation)` | `isRoot`, `parents`, `parts`, `designs`, `definitions`, `usedBy`, `calls`, `calledBy`, `keptBy`, `rivals` (one list each); `beside`, `above` are functions of the view (`Views.beside`) |
| `ProofView` | `status`, `results`, `findings`, `examples`, `authored` | `status`, `obligations`, `messages`, `examples`, `proof` |
| `CodeView` | `shown: Shown`, `runCheck`, `report` | `codeProof`, `trusted`, `tested`, `runtime`, `implementationProof` |
| `ReviewView` | `standing`, `decision`, `waitsFor`, `notMechanical` | `Reviewed`'s state, causes, decision, wait |

- `Overview` is six fields of `Tally[K]` (a commutative monoid) by concept; `Views.overview` is one `foldMap` each.
- `tree` and `inbox` are functions of `View` in `Views`.
- The snapshot (`.frflow/kb.json`, DAG §4) is rows of `wire`'s own: `Snapshot(kb, root, definitions, trusted,
  vocabulary, nodes)`, each `SnapNode(header, place, check, body)`: the `Header` (id, kind, hash, content), the
  `PlaceRow` (parents, parts, uses, relies, covers, exempts), the `CheckRow` (status, `holds`, each obligation with its
  statement) and a `Body` by kind (`Claim`, `Invariant`, `Contract`, `Assumption` with its examples and code,
  `Definition`, `Design`, each with only its fields). `wire.snapshot.Rows` is the one mapping from domain values, so
  the codecs are in the rows' companions (no orphan instances) and a domain change reaches the export only through
  `Rows`. Today's per-node `split` is not repeated: it is the split's obligations' statuses. The front ends' `--json`
  prints these rows; the `api.node` views are never encoded. It is an export for tools; no FrFlow module reads it
  back.
- The API is three algebras, held together by `FrFlowApi[F](reading, deciding, proving)`:

| Algebra | Operations | Today's |
|---|---|---|
| `Reading` | `view`, `diff(node)` (field diffs and the governed code's `git diff` since the decision's commit), `find(words)`, `modelFingerprint` (the web view's stale-model guard) | `tree`, `show`, `inbox`, `diff`, `find`, `modelFingerprint` |
| `Deciding` | `developer(as)`, `preview(command, by)`, `decide(command, by)` | `decide`, `preview`, the developer's name |
| `Proving` | `render`, `status` (writes the snapshot, returns the view), `check(only): Stream[F, CheckEvent]`, `ci: Stream[F, CheckEvent]`, `scaffold(node)` | `render`, `status`, `check(…, progress)`, `ci(progress)`, `scaffold` |

### 4.6 Error model

| Where | Type | Channel |
|---|---|---|
| elaboration | `ElabError(at: Site, fault: Fault)`; `Fault`: `DeclaredLater`, `NoType`, `FunctionEquality`, `NotData`, `ValueReadWhileBuilding`, `BadPath`, `OutsideStep`, `Thrown` | `ValidatedNec`, all collected; faults travel unplaced on terms and in `Failure` until `Elab` places them |
| structure | `analysis.Problem` (cases with data; for invariants `NotKeptInScope`, `NoKeeper`, `ScopeOutside`, `ExemptWrongKind`, `NamedTwice`, `ExemptWithoutReason`; `DeclaredTwice`; `DataForCodeOnly`, data given for a symbol
only plain code reads) | `ValidatedNec` |
| both, at the shell | `Problems.NotElaborated / Invalid` | raised in `F` (`NoStackTrace`): no operation can continue |
| evaluation | `EvalError` (`Quantified`, `Unbound`, `NoDefine`), a plain enum | `Either` in `Compiled.run` |
| a flow's run | `FlowError` (`NotEvaluated(EvalError)`, `NotBound`, `NoOperation`) | raised in `F` (`NoStackTrace`) |
| decisions | `Refusal` | `Either`: the caller says it and goes on |
| a check | `Finding` cases in `Judged` and `NodeCheck` (`ProofNotAllowed(List[(line, NotAllowed)])`, `LeanAndScalaDisagree`, …); `Result.messages` are Lean's diagnostics; `NotAllowed.LemmaImport` for the shared lemmas | data |
| tests | `TestReport` with `Against`, `Failure(inputs: List[Value], broke: Broken, …)`, `Made(ty, says)`; `Broken` is `eval.run`'s, shared with examples and run time | data |
| plain code calling a define with no Scala value | `NotEvaluated(EvalError)`, thrown by `Applied.called` | the plain-code path has no `Either` to return (the documented edge) |
| wiring a service | `WiringError` | `Either`; the facade syntax throws it when wired (the documented edge) |
| a broken contract at run time | `Violation` reported, then `ContractViolation` thrown | the service is a plain Scala function; fail closed |
| shell faults (no Lean, unknown node) | `FrFlowError` (`NoStackTrace`) | raised in `F` |
| FrFlow bugs | `IllegalStateException` with "FrFlow bug" | only where the types rule the case out |

Text for the developer is made only in `cli` and `web` (R4). Two kinds of text are data and stay: what the developer
wrote (a reason, a `describedAs`, an exception's message from their code, `Broken.Threw`) and
generated Lean (each obligation's doc comment, made with the obligation by `Required`, `Tries` and `Idle`, as today).

### 4.7 Effects: where `F[_]` is used, and why

The core (`core`, `dsl`, `proof`, `decision`, `Denote`, the `testing` generators) has no effect type. Where an `F[_]`
appears, the table names what pays for it:

| Algebra or program | Why over `F[_]` | Second interpreter / law / restriction |
|---|---|---|
| `ProjectFiles[F]` | the checker's programs are tested without a disk | in-memory; law: a read after a write gives what was written |
| `Lake[F]` (`Resource`) | the check's planning, caching and judges are tested without Lean | scripted interpreter answering by module |
| `Git[F]` | decision and review tests without a repository | in-memory |
| `LedgerStore[F]` (`Resource` holding the lock) | the CLI and the web view may decide at once | in-memory; law: `update` stores only on `Right`, concurrent updates are serialized |
| `KeyRing[F]` | tests never touch the developer's key | key made in memory; signing and verifying pure once read |
| `ReadInputs`, `Evaluate`, `CheckProgram`, `NodeChecker`, `DecideProgram` | programs | ask only `Monad`, `Parallel`, `Clock`; cannot do what their algebras do not |
| `FrFlowApi[F]` | the CLI, web and agent suites | in-memory interpreter; law: what `preview` shows is what `decide` records |
| `FlowInterpreter[F]` | the developer's flows run in `SyncIO` (examples, tests) and `IO` (production, interleavings) | one class, two constructions: `FlowRun.sequential[F: Sync]`, `FlowRun.concurrent[F: Async]` |
| `Examples[F]`, `Interleavings[F]` | classes over a `FlowInterpreter[F]`, not algebras: each has one implementation | `Sync`; `Interleavings` `Async` + `Random`, deterministic under `TestControl` |

Concrete `IO`: the web server's wiring (http4s routes and `serve`), the CLI's `main` (the composition root that fixes
`F = IO`), and the terminal. The run-time services stay synchronous functions (`Running.service`), since the
developer's plain code calls them.

### 4.8 Choices with a real trade-off

**A. Encoding of terms and flows.**
(1) Initial: the DSL builds `Expr` and `Prog` values; back ends are folds. (2) Tagless final (`trait Sym[R[_]]`, user
code `def f[R[_]: Sym]`). FrFlow hashes terms, compares them, flattens conjunctions, substitutes operations for
`idle`, derives commutation obligations from parallel steps, and finds what a term mentions; under (2) each of these
is another interpreter, and rewriting needs the final-to-initial round trip. (2) would also change every example's
source, hence every decided content. **Recommendation: (1).** Production flows stay higher-order (`Flow`, run by
`FlowInterpreter` as written): they are only run, never printed or analysed.

**B. Ambient state and reflection.**
(1) Two named scopes, each a `ThreadLocal` set for the duration of one call: `dsl.build.Fresh` (fresh variables while
elaborating, and while an implementation's flow is built during a run) and `dsl.term.Values` (the values in force
where plain code runs, as today's `Bindings`); plus two memos in immutable values (`Def.compiled`, an atomic `Once`;
`KnowledgeBase.elaborated`, a `lazy val`); and, in a running service, the watch's cell (`AssumptionWatch.held`) and the
samplers' counters (`Sampling.of`), the only shared mutable state of `runtime`. Reflection on the developer's code is one use: `Captures` reads what a flow's
lambda captures (today's `Lambdas.captured`), so a value named in a for-comprehension becomes one `let` in Lean.
Parameter names and a define's name are read at compile time (`Source.of`, `Source.valName`). (2) Pure: terms as
`State[VarId, Expr]`, or Axelsson–Claessen's numbering from the body; values passed to plain code as an argument.
(2) loses the object identity sharing depends on; Axelsson–Claessen calls each lambda twice per level, exponential in
nesting depth; and `p.value` without a scope changes every example's plain code. **Recommendation: (1)**, the two
scopes allow-listed by the architecture test, nowhere else.

**C. Boundaries.**
(1) Keep the user's trait of operations over terms (`trait Database { def load: Flow[CrmStore] }`), with its
signatures and the vocabulary their types declare derived at compile time (`BoundaryOps[T]`, a macro over the trait's
methods: no Java reflection, no registry) and the proxy typed `Boundary[T] & T`; production implementations return
DSL flows with `Flow.effect(x)(f)`. (2) Tagless boundaries, `trait Database[F[_], T[_]]`, with `Database[Flow, Term]`
for the model and `Database[IO, Id]` for production. (2) changes the examples' traits and implementations (crm,
sharing), so their governed code moves and the design nodes governing them come back once. **Recommendation: (1) now,
(2) as a later, separate proposal.**

**D. How far in one step.**
(1) Strangler: the new IR and phases introduced behind the existing DSL surface, one representation at a time, each
step pinned by golden files of the examples. (2) A new repository built from the planned core, examples ported at the
end. (2) is faster to write and loses the guarantee that Lean, contents and ledgers stay the same at every step.
**Recommendation: (1)**, section 6.

**E. Module granularity.**
(1) Thirteen modules as in 4.3. (2) Six modules (`core` with DSL, analysis and obligations; `lean`; `run` with
evaluation, run time and testing; `decision`; `shell` with wire, project and api; `front`), boundaries inside them
checked by the package test only. (1) makes the compiler enforce that production code cannot reach Lean or the ledger
and that `decision` cannot see the IR; (2) has fewer build entries. **Recommendation: (1).**

**F. Code fingerprint.**
(1) Scala without comments, each line's indentation as written, runs of spaces collapsed outside literals
(`ScalaTokens`, over a small lexer of comments and literals). (2) The Scala 3 compiler's or scalameta's tokenizer, with
its indentation tokens. (3) A hash of the compiled TASTy. (2) is exact but adds a parser dependency to the shell; (3)
ignores renaming of locals but moves with every compiler upgrade and needs compiled output. **Recommendation: (1)**:
line breaks and indentation are hashed, so every change Scala 3's indentation syntax makes significant moves it.

**G. Moving existing decisions to the new content form and fingerprint.**
(1) A signed `confirm --rebind` (`Command.Rebind`): every accepted node whose decision is unmoved is confirmed with
its content in `V2` and its code by tokens, one decision per node, signed by the developer. (2) Silent: compare old
decisions on the common fields forever. (2) keeps working for content (`Formats.aligned`), but a `Text` fingerprint
still moves on the first comment edit, which is the reported bug, and a `V1` decision cannot see an edit of
`.leftOpenAbove` or of a failure clause (in `V1` they are only in the dropped `definition` text). **Recommendation:
(1)**, with (2) as what happens until the developer runs it; `status` warns while decisions in the old form remain
(`Warning.OldForm`).

### 4.9 Decisions: content, signatures, fingerprints, review, rules

**Content and its form.** `Content(fields: List[(String, FieldValue)])` with three field shapes (text, texts,
record) matching every value in the examples' ledgers; `Canonical.print` is byte for byte today's
`protocol.Canonical`. A content's form is read off its fields (`Formats.of`: `V1` has a `definition` field, which
today's `Contents.of` writes for every kind; `V2` does not), so no new field is stored and the form is covered by the
signature through `content.ref`. Step 0 checks the rule on the four examples' ledgers.

- `V1` is today's projection, kept until step 12.
- `V2` is `project.pipeline.Contents.of`: today's fields in today's order with today's texts (`kind`, `parents`,
  `parts`, `statement`, `why`, `sources`, `substitutions`, `examples`, `vocabulary`, `uses`, `governs`, `op`,
  `replaces`, `keeps`, `expects`, then `reliance` and `failure`, then `implementation`, `model`, `implementations`,
  `runtime`), less the retired `definition`, `idea`, `ideaSection`, `notModelled`. The fields whose texts are today's
  renderings of values (`Example.describe`, the Scala type text of `uses`, the boundary model's Lean, `Keep.describe`,
  `RunCheck.describe`) are one function each in `Texts`, pinned per node by the step-0 golden. `vocabulary` is written
  (`Texts.vocabulary`): `name: means` of every opaque type and symbol the node speaks of, sorted, as today's
  `termsOf(n) ++ n.defines`: what its statement mentions through its defines, its operation, the terms it defines, and
  the opaque types of the rules of the invariants it keeps. `VocabularySuite` pins it against auth's ledger (a
  definition, `GrantTable`; a claim, `AccessExactly`); the step-0 golden pins it for every node.
- `Formats.aligned(decided, now)` compares a `V1` decision with today's content on the fields both have; `V2` as is.
  So removing `idea = "…"` from a node's source, or the `IDEA.md` section a content held, moves no decision.
- `Meaning.own` (cause `self`) is the content without `parts` and `parents`; a design keeps its `parents`, since
  placing a design is what is decided and its chain is empty (DAG §5). No `.under(...)` text needs stripping: the
  regex is deleted.

**Old `IDEA` entries.** The ledger codec reads and writes them unchanged (the file's bytes round-trip).
`decision.ledger.Retired.ids = {IDEA}`: never a subject, never listed as gone (`Reading.gone`), refused by
`gone IDEA` as an unknown node. Their signatures still verify.

**Signatures.** `Payload.of(id, d)` joins, with NUL, exactly today's fields in today's order: node id, action, by, at,
reason, rejected, chain, code fingerprint, commit, after, `content.ref`. A golden test verifies every signature of the
four examples' ledgers through it. `Seals.signAdded(before, after, sign)` signs the decisions `after` has that `before`
did not, once `Ledger.add` has set their `after`; `Decide.added` lists them for the shell to report, subjects parents
first and then gone nodes. Verifying is `Seals.verify(check)(id, d)`, pure; `DecideProgram` asks `KeyRing` for the
signer only after the rules accepted the command, so a refused command never creates a key.

**Fingerprints.** `CodeFingerprints.of(files)` hashes the governed files, sorted, each as `path NUL text` with a
missing file as `<missing>`, twice: raw (`Text`, today's exact hash) and by `ScalaTokens.significant` (`Tokens`,
stored with the prefix `tokens:`). `ScalaTokens` blanks comments (a comment becomes a space, a newline in it stays),
drops blank lines and trailing spaces, keeps each line's indentation as written (tabs too), and collapses runs of
spaces outside literals. Law, in the direction that matters: an edit that changes what the program means always moves
the fingerprint; edits of comments, blank lines and spacing between tokens do not. Some harmless edits do move it
(`f(/*a*/x)` to `f(x)`, tabs to spaces). `Governance.of` gives today's file set exactly; `CodeNow.matches` compares a
decision with the form it recorded.

**Review states.** `Standings(subjects, ledger).all` folds the subjects parents first. Causes: `self`, `above` (the
chain moved, unless only words moved above: `Reworded.only` recomputes the chain with the reworded nodes' meanings as
they were when the decision was taken), `parts`, `code`, `revisit`, `merged`, and a parent rejected.

**Rules.** `Decide(reading, command, author)` refuses a reason of fewer than three words (`Reason.enough`, today's
`tooFew`), then applies one rule class per `Command`: `Accepting` (`accept` with `--revisit`, the mechanical batch
`confirm`), `Rejecting`, `Revisiting`, `Removing` (`gone`) and `Rebinding` (`confirm --rebind`); `Below` settles what
moved only with an accepted node. A rule makes each decision with `Decision.taken(action, author, reason,
reading.bound(subject))`. The checks reach the mechanical rule as `Subject.proof:
ProofStanding(unproven, partsMake)`, made by `project.pipeline.ReadProof` line for line as today's `Proofs.unproven`
and `partsMake`: `Unproven` has one case per line (the check, `complete`, a `needed_C` shown, a clash, nothing below,
failing examples on the promise or the code, a keep not proven by the keep's own status, the implementation, the
root's code, tests, an expectation, idle), and `partsMake` is `complete` proven, every `needed_C` not shown, no clash
shown. `Mechanical.why(reading, subject, others)` is today's chain in its order: a choice held, not under review,
causes beyond `self`/`above`/`parts`, the meaning moved, `parts` among the causes without `partsMake`, not proven
again (nothing below aside), a wait for a node the batch does not accept first; `Reading.notMechanical` folds it
parents first. Today's two later clauses (examples, invariants) are only reached through `unproven`, which holds
them, so they are not repeated. Still `???`: `Reading.waitsFor`, `Meaning.decisionMoved`, `Below.movedOnlyWith`,
ports of today's `Reading`, `Meaning` and `Decide`.

### 4.10 Patterns

The code uses few patterns, each the same way everywhere. One file shows each.

| Pattern | What it is | Example |
|---|---|---|
| Phase | a verb-named object applied to one stage type, giving the next; pure; private helpers below, one idea each | `core/analysis/Validate.scala` |
| Value of | a noun-named type made by `X.of(…)` in its companion | `core/analysis/Shown.scala` |
| Stage type | made only by its phase: an opaque type or a `private[analysis]` constructor | `core/analysis/Valid.scala` |
| Case per kind | an `enum` with only the data of each case; what varies by kind is one match | `core/spec/Statement.scala` |
| Gathered from parts | a `Monoid`, combined with `foldMap` or by every operation | `dsl/build/Declarations.scala` |
| Built later, errors kept | `Deferred[A]`, an `Applicative`; parts combined with `mapN`/`traverse`; a fault before its site is known is a `Fault`, placed once | `dsl/kb/Elaborate.scala`, `dsl/shape/Elab.scala` |
| Interpreter of the IR | a fold over `Expr`/`Prog`/`Prop`, state only where names are made (`State[Naming, _]`) or terms are met (`Writer[OpenTerms, _]`) | `proof/lean/lower/Lower.scala`, `proof/lean/lower/LowerProp.scala` |
| Algebra | `trait X[F[_]]` with its laws in the doc, interpreters `make`/`inMemory` in the companion | `project/port/LedgerStore.scala` |
| Program | a class over algebras asking the least capability, a `for` of steps | `project/program/DecideProgram.scala` |
| Rule per command | one dispatch match, one class per case returning `Either[Refusal, Ledger]` | `decision/rules/Decide.scala` |
| Derived view | a case class of what front ends show, one function per group | `api/node/NodeViews.scala` |
| Errors as cases | an enum with data; text only in `cli` and `web` | `decision/rules/Refusal.scala` |

Names: one name per concept, none shadowing the standard library (`Iteration.Forall`, not `Some`; `ScalaCode`, not
`Runnable`); one `OpSig` (`core.vocab`). Lean atoms the lowering spells itself go through `lower.Atoms`.

### 4.11 The planned code

`planned/` (build in `planned/build.sbt`, sources under `src/<module>/`, suites under `test/<module>/`). What to read first:

| File | What it shows |
|---|---|
| `core/frflow/core/expr/Expr.scala`, `Prog.scala`, `PrimOp.scala`, `Iteration.scala`, `Exprs.scala`, `Mentions.scala` | the IR, one operator per meaning |
| `core/frflow/core/spec/Statement.scala`, `Node.scala`, `Promise.scala`; `example/CallExample.scala`, `RunExample.scala` | a node, one case per kind |
| `core/frflow/core/code/Code.scala`, `CodeTable.scala`; `analysis/Shown.scala` | attached code, shown piece by piece |
| `core/frflow/core/analysis/Validate.scala`, `Scope.scala`, `Resolve.scala`, `InForce.scala` | stage types; the invariant-scope rule on types |
| `dsl/frflow/dsl/build/Deferred.scala`, `Fault.scala`, `Site.scala`, `Declarations.scala`, `Source.scala`, `Fresh.scala`; `term/Term.scala`, `Notes.scala`, `Param.scala`, `Values.scala`, `Def.scala`; `shape/CallShape.scala`, `DefineShape.scala`, `Elab.scala`, `Defines.scala`; `node/Node.scala`, `NodeSyntax.scala`, `OnPromise.scala`; `flow/Flow.scala`, `BoundaryOps.scala`; `kb/Elaborate.scala` | the surface and elaboration, with no registry and one error shape |
| `eval/frflow/eval/Denote.scala`, `Env.scala`, `Fn.scala`, `DefSyntax.scala`; `run/FlowInterpreter.scala`, `FlowRun.scala`, `Examples.scala`, `CallCheck.scala`, `Kept.scala`, `Givens.scala`, `PromiseExamples.scala`, `CodeExamples.scala` | the Scala meaning; production flows run directly, sequentially or concurrently; examples on the promise and the code |
| `runtime/frflow/runtime/Running.scala`, `Service.scala`, `Guard.scala`, `Wiring.scala`; `check/CallValues.scala`, `AssumptionWatch.scala`, `Sampling.scala` | today's `enforce`, one job per function, its state named |
| `proof/frflow/proof/obligation/Prop.scala`, `Obligation.scala`, `Required.scala`, `Tries.scala`, `Idle.scala`; `terms/TermTable.scala`, `Terms.scala` | obligations as data, each with its sentence, and what their declarations are applied to |
| `proof/frflow/proof/lean/ast/*`, `lower/Lower.scala`, `lower/LowerProg.scala`, `lower/LowerProp.scala`, `lower/LowerObligation.scala`, `print/Print.scala` | the Lean back end |
| `proof/frflow/proof/reading/ProofRules.scala`, `NotAllowed.scala`, `LeanSource.scala` | today's proof-file rules, one case each |
| `decision/frflow/decision/content/Formats.scala`; `ledger/Payload.scala`, `Seals.scala`, `Retired.scala` | content forms, signatures, the old `IDEA` |
| `decision/frflow/decision/review/Standings.scala`, `Meaning.scala`, `Reworded.scala`; `rules/Decide.scala`, `Accepting.scala` | review as a fold, one rule per command |
| `decision/frflow/decision/review/Mechanical.scala`, `ProofStanding.scala`, `Unproven.scala` | the mechanical rule, as today's |
| `project/frflow/project/pipeline/Contents.scala`, `ReadSubjects.scala`, `ReadProof.scala`, `Analysis.scala`; `code/ScalaTokens.scala`, `Governance.scala` | the `V2` content, the subjects, fingerprints |
| `project/frflow/project/port/*.scala`, `program/*.scala` | algebras, programs with least capability |
| `api/frflow/api/*.scala`, `view/Views.scala`, `node/NodeViews.scala`, `node/Placement.scala`; `wire/frflow/wire/snapshot/*`, `Rows.scala` | the API, the node views, the snapshot's rows and their one mapping |
| `test/proof/frflow/proof/lean/CrmModulesSuite.scala`, `ExpiryIr.scala`; `test/proof/frflow/proof/reading/ProofRulesSuite.scala`; `test/decision/frflow/decision/*`; `test/dsl/frflow/dsl/node/PromiseSyntaxSuite.scala`; `test/project/frflow/project/pipeline/VocabularySuite.scala`; `test/eval/frflow/eval/run/CodeExamplesSuite.scala`; `test/runtime/frflow/runtime/ServiceSuite.scala`, `Search.scala` | the evidence |

**The Lean evidence.** `CrmModulesSuite` builds four modules of `examples/crm/lean/FrFlowGen/Crm/` as ASTs and compares
`Print.module` with the files, copied unchanged into `test/proof/resources/crm/`:

- `Boundaries.lean`: `class Database (m : Type → Type)` with its operations, the `DatabaseModel` namespace of `do`
  defs, `structure World`, `instance : Database (StateM World) where logEvent e := …` (fields with parameters,
  `FrFlow.within` with a structure update `{ w with database := s }`), and three `@[frflow_defs] theorem
  Database.load_onWorld … := rfl` with parameters and a line break before `rfl`;
- `Domain/Def_expireOnce.lean`: `def expireOnce {m : Type → Type} [Monad m] [Database m] (expire : …)`, its body
  lowered by `LowerProg` from hand-written `Prog`;
- `Domain/Def_expireOnce_run.lean`: the run on the models (`FrFlow.runOn`);
- `ExpiryJob/Spec.lean`: the post lowered by `Lower` from hand-written `Expr`, the claim, and the obligations `impl`
  and `unsat` lowered by `LowerObligation` from `Prop` over a `TermTable`: the claim applied to its open terms, the
  operation `runExpiry` replaced by `(Crm.expireOnce_run expire)`, the binders `(expire : CrmStore → Int → CrmStore)`
  met in order, the hypothesis `(h_SharesExpire : (Crm.SharesExpire.claim expire))`, `¬ (…)`, `namespace Obl`, and
  the doc comments ("Every result of expireOnce_run meets ExpiryJob, given what SharesExpire promise.").

`LExpr` has no raw-text case (`Num` and `Str` are its only literals). Two AST parts hold text, both FrFlow's own and
never built from a model: `Proof.Tactics` lines and `Preamble`'s options.

**Measured** (`tools/budget.py` over `planned/`): no file over 200 lines or 120 columns, no parameter list over
four, one type per file (private helpers aside), every package 3 to 15 files (the facade `frflow` is one file). Over
20 lines are only five single matches over an enum: `Exprs.children`, `Exprs.typeOf`, `Lower.expr`, `LowerPrim.apply`,
`Print.expr`. Casts (`asInstanceOf`) are in six places, each with its reason: `eval.Fn` (values typed by the IR: `bool`,
`pairs`, and the developer's functions called and made, `call` and `of`; nothing else in `eval` or `runtime` casts),
`eval.run.FlowInterpreter` (a bind's result term, typed by the step), `dsl.shape.CallShape` and
`dsl.shape.DefineShape` (a lambda's binders, made of exactly the shape's types), `dsl.term.Param.value` (a value bound by its own `bind`),
`dsl.flow.Flow.effect` (an effect's argument values, typed by its terms).

**Size projection.** Today: 12,008 main lines in 347 files. The planned code is the skeleton; the ports the `???`
stand for are estimated from the code they replace:

| Module | Planned now (files / lines / `???`) | Projected lines | Replaces today |
|---|---|---|---|
| `core` | 89 / 1,390 / 2 | 1,550 | parts of `model` (IR, vocabulary, validation), `protocol` (`Walk`, `NodeKind`, `RunCheck`) |
| `dsl` | 52 / 839 / 11 | 1,600 | `model`'s DSL, derivation, source macros (arities 0 to 6 written out) |
| `proof` | 72 / 1,592 / 16 | 2,100 | `lean`, `model`'s `LeanPrinter`, `Types`, `Names` |
| `eval` | 27 / 578 / 8 | 700 | `model`'s `Eval`, examples, flows |
| `testing` | 12 / 105 / 1 | 650 | `model`'s `testing` |
| `runtime` | 14 / 309 / 1 | 400 | `model`'s `runtime`, `Node.enforce` |
| `decision` | 44 / 702 / 3 | 850 | `ledger`, `protocol.decision` |
| `wire` | 15 / 168 / 0 | 550 | `protocol`'s codecs |
| `project` | 26 / 614 / 17 | 1,100 | `check` |
| `api` | 21 / 274 / 3 | 450 | `api` |
| `cli`, `web`, `agent` | — | 1,700 | the same, less `IdeaSources` and the question numbers |
| total | 372 / 6,571 / 62 | about 11,650 | 12,008 |

The result is about the same size (about 3% smaller), in about 520 files instead of 347: smaller files, no type with
more than six fields, and every concept in one place. Grouping a phase's small case types into its file where the
skill allows (a sealed family) would bring the count nearer today's; the plan does not require it.

## 5. Feature audit

The full table is `features.md`. Every feature an example or a documented workflow uses has a concept and stays.
Drop candidates, none used by an example: `race` (with the `Races` boundary), `guarantee`/`bracket`, `timeout`,
`parTupled`, `Flow.ifM`. Moves: `checkedAtRunTime` to the code attachment (or drop: unused), `testedWith` to the
checker's configuration, `reporting` to `runtime`. Removed at the owner's request: `IDEA.md` as a FrFlow concept
(`idea = …`, `KnowledgeBase(…, idea = …)`, `accept IDEA`, idea sections and their warnings, `ask --idea`, `From:`
lines) and numbered questions in the agent layer. Behaviour change, asked for: comment-only and formatting edits of
governed files no longer bring nodes back (after `confirm --rebind`). `examples/rebac` is not a candidate: it is
untracked derived output with nothing in the repository.

## 6. Implementation plan

Each step is one reviewable change, green on `sbt test` and `sbt leanTest`, and keeps the golden outputs of step 0
unless it says otherwise. "Suites" says which of FrFlow's suites (5,176 lines) and the examples' (1,226 lines) change.
Until step 17 the examples' tests compile against a compatibility facade, `frflow.compat`, exported by the facade
package: `knowledge.exampleResults`, `.test`, `.parts`, `.problems`, `.parentsOf`, `.termsOf`, and type aliases for
`frflow.check.Workspace`, `frflow.api.LiveApi`, `frflow.protocol.{NodeId, NodeKind, ReviewState}`, `frflow.Node[?]`,
each delegating to whatever implements it at that step.

0. **Pin behaviour.** `GoldenExamplesSuite` (check module, tagged `Lean` where it needs Lean), for auth, keycloak, crm
   and sharing: the hash of every generated Lean file and proof stub; each node's content `ref` and `hash`; each
   node's code fingerprint as today (`Text`); every decision's signature verified through a copy of today's payload;
   every stored content having `definition` (the rule `Formats.of` rests on); each node's review state and causes; the
   snapshot JSON without `exportedAt`; `tree`, `status`, `inbox --json` and text; a ledger round trip (read and write
   give the same bytes). `ArchitectureSuite` (section 7) with today's edges as its allowed list. Test dependencies
   `cats-laws`, `discipline-munit`, `munit-scalacheck`, `munit-cats-effect`. Suites: three added.
1. **Delete the drop candidates the owner approves** (`race`/`Races`, `guarantee`/`bracket`, `timeout`, `parTupled`,
   `ifM`). Golden unchanged. Deletes their `Steps` cases, printer and runner branches. Suites: their cases in
   `model`'s flow suites deleted.
2. **Give each module its own top package** (`frflow.model`, `frflow.lean`, `frflow.check`, …; the facade `frflow`
   keeps exporting the DSL, so models still `import frflow.*`), and replace `private[frflow]` by the module's package.
   The 40 cross-module uses of internals become public API of `model`, named in the architecture test as debt. Suites:
   imports only; `frflow.compat` added for the examples' tests.
3. **Create `core` with the IR**: names, `Ty`, `Value`, `Expr`, `Prog`, `Mentions`, `Exprs`, `Progs`, and a
   translation `Tree/Steps → Expr/Prog` inside `model` (today's paired operators map to one `PrimOp` each, today's
   list operations with a function argument to `Iterate`). Property tests: `typeOf` total, `Mentions` monoid laws,
   `Progs.sequential` of a translated `Par` equals today's stored reading. Deletes nothing.
4. **Mentions from the IR.** `Lifted`'s `paramObjects`, `defs`, `opaques`, `types`, `boundaries`, `errors`, `commutes`
   come from `Exprs.mentions` and `Progs` over the translation; `KnowledgeBase` and `Validation` stop reading printed
   text (`Scope` replaces `inScope`). Golden identical. Deletes the regexes in `Validation.vocabulary` and
   `KnowledgeBase.inScope`, and the `Printed` fields only those read. Suites: `model`'s validation suite unchanged.
5. **The Lean AST, lowering and printing** over `Expr` and `Prog`, called by `LeanPrinter`'s callers through the
   translation. Golden Lean identical, fixtures and examples. Deletes `LeanPrinter`, `Types`' Lean half, `Names`,
   `Printed`, `Walked`. Suites: `CrmModulesSuite` extended to one example module per kind (`Types`, a `Def_`, a
   `Term_`, `Boundaries`, and a node's `Spec`, `Auto`, `Theorems`, `Impl`, `Checks`, `Eval`, and `RootImpl`), since
   `NodeModules`, `VocabularyModules` and `RootImplModule` decide the order of declarations and imports; per-case
   lowering tests added; `model`'s printer suites deleted (their cases kept as lowering tests).
6. **The Scala meaning and the plain-code path.** `eval.Denote` over `Expr` with an explicit `Env`; `Literals` and
   `Reflect`; coverage as returned `Hits`; `Bindings` becomes `Values` behind `Param.value`; `d.fn` through
   `Def.compiled`; `FlowInterpreter` runs `Prog` and DSL `Flow`s with `Effect` steps, call arguments bound as typed
   run-time symbols. Golden identical (examples' results are in the snapshot). Deletes `Eval.scala`, `Watch`,
   `Steps.Outside`, `Flows.run`. Suites: `model`'s eval and flow suites move to `eval`, same cases.
7. **The `decision` module** reading `Subject`s, with a temporary adapter `SubjectsFromSnapshot` (`SnapNode` →
   `Subject`) in `ledger` until step 9. `Content` (`V1` only), `Decision`, `Ledger`, `Payload`, `Seals`, `Standings`
   with `Reworded`, `Decide` with one rule per `Command`, `Retired`. Golden: ledger round trip, review states and
   causes, every signature verifies. Deletes `ledger.review.Graph`, `protocol.decision.Ledger`'s logic, `CodeProof`'s
   string parsing (replaced by `Shown` at step 9; until then the adapter carries today's strings). Suites: `ledger`'s
   decide and standing suites rewritten over `Subject` with the same cases.
8. **Statements and nodes.** The DSL builds `Node[S, F]` and `Def`s named by `Source.valName`; `Elaborate` produces
   `spec.Node`s, `Edge`s and the vocabulary from `Declarations`; `BoundaryOps` derived; `V1` contents reproduced byte
   for byte (the `definition` excerpt still cut from the source, the idea fields still read). Golden: contents
   identical. Deletes `node/Node.scala`, `Keep`, `ModelOf`, `ModelNode`, `ModelFor`, `AssumptionOn`, the `require`s,
   `LeanType.known`, `LeanType.ofJava`, `Lambdas.valName` and the reflection on lambdas' parameter names. Suites:
   `model`'s node and knowledge-base suites rewritten over `Elaborate`; the examples' tests unchanged through
   `frflow.compat`.
9. **Code attachments** (`CodeTable`) and `Shown`; `ReadSubjects` replaces the step-7 adapter, its `ReadProof`
   giving `Unproven` line for line as `Proofs.unproven`, so the batch `confirm` takes the same nodes (golden `inbox`
   and `confirm` identical; no behaviour change). Deletes
   `Implementation`'s string `wiring` and "last file" convention, `Testing.testable`'s duplicate logic,
   `Snapshots.tested`, `SubjectsFromSnapshot`.
10. **`Validate` and `Resolve`** replace `Validation`, `inForce`, `provisional`, `ordered`, `calledBy`,
    `definitionsUsed`. Problems are reported all at once, each with today's message. Deletes those members of
    `KnowledgeBase`.
11. **Obligations as `Prop`; modules as `LeanModule`**, with `TermTable` and the evaluations as inputs. Golden Lean
    identical, so check hashes do not move and nothing is re-checked. Deletes `Ctx`, `Vocabulary.resolve` and `⟦⟧`,
    `lean.LeanType`, `LeanText.conjuncts`, `Refinement`'s strings, `Evals`' text. The proof-file rules become
    `NotAllowed` cases, today's allow-lists unchanged. Suites: `lean`'s obligation suites rewritten on `Prop`, a test
    per try kind pinning set and order, a test per proof-file rule.
12. **Content `V2`, token fingerprints, `confirm --rebind`, and `IDEA.md` removed**, in one change, so no version
    reads `V2` contents while `IDEA.md` still exists (an edit of an idea section stops bringing nodes back in the
    same change that removes idea sections). New decisions record `V2` and `Tokens`; old ones are compared through
    `Formats.aligned` and `CodeNow.matches`. In the same change:
    - code: `Contents.definition` (the source cutting) and `Meaning.own`'s regex deleted; `Node(…, idea = …)` and
      `KnowledgeBase(…, idea = …)` parameters, `Idea`, `IdeaDecision`, `IdeaReview`, the idea warnings in
      `Governance`, `accept IDEA`, `ask --idea`, the `IDEA` rows of `inbox`/`review`, the agent's `IdeaSources`
      deleted; old `IDEA` entries handled by `Retired`;
    - examples: every `idea = "…"` argument deleted (77 across the four); `README.md` written from `IDEA.md` for auth,
      keycloak and crm, and merged into sharing's existing `README.md`, with the 13 `From:` lines (all in sharing)
      dropped; `IDEA.md` deleted. Ten node texts (`why`) say "the idea" (`auth/Auth.scala:17` and `:38`,
      `crm/Writes.scala:23`, `crm/Expiry.scala:11`, `crm/Crm.scala:262`, `:300`, `:306`,
      `keycloak/Introspection.scala:28`, `keycloak/Access.scala:23`, `sharing/Purpose.scala:70`); they are left as
      they are (rewording them would bring the nodes back for review), and now point at the README. The owner may
      reword them later as decisions of their own;
    - docs: `docs/USAGE.md` (the workflow loses its `IDEA.md` steps, `accept IDEA`, the `self` cause's "its section of
      the idea", the idea warnings, the agent's `From:` paragraph; adds `confirm --rebind`), `docs/DAG.md` (9
      mentions), `docs/index.html` (40), the frflow skill (`.claude/skills/frflow/SKILL.md`, 22: the root is written
      from the developer's description, the README is optional prose), `frflowInit` (the empty knowledge base without
      `idea`, "next: propose the root") and `frflowInitAgent` (the agent writes a README draft and proposes the root);
    - the agent layer: questions have no numbers; `asked QUESTION --assume ANSWER` records a question, `replied
      QUESTION TEXT` names it by its words (a unique prefix, as `find` matches); listings show the question's text;
      conversation records are not referenced from any file.

    Golden: review states identical (no decision moves: `V1` decisions are compared without `definition` and the idea
    fields); contents change to `V2` (listed per node); Lean identical; `inbox` and `status` lose the `IDEA` lines
    (listed). Then the owner runs `confirm --rebind -m "…"` on each example's ledger with his key, outside the change,
    and commits the four ledgers. Suites: `ledger`'s idea suites and the agent's `IdeaSources` suite deleted;
    `AgentCliSuite` and `AgendaSuite` rewritten without `Q1`.
13. **Algebras and programs in `project`** (from `check`): `ProjectFiles`, `Lake`, `Git`, `LedgerStore`, `KeyRing` with
    in-memory interpreters and law suites; `ReadInputs`, `Evaluate`, `CheckProgram`, `NodeChecker`, `DecideProgram`.
    Deletes `Disk`, `JsonStore`, `KeyStore`, `check.Analysis`, `sys.env` reads outside `Config`. Suites: `check`'s
    suites run against the in-memory interpreters; those needing Lean stay tagged.
14. **`testing` and `runtime` modules.** `Gen` as data with `Draw`; `testedWith` to configuration; `Running`,
    `Service` (with `Guard` and `runtime.check`), `Interleavings` over `FlowRun.concurrent`; the facade keeps `knowledge.service(...)` and
    `knowledge.run[F](...)`. Deletes `kb.test`, `kb.service` members, `Wiring` in `model`, `Node.enforce`,
    `unsafeRunSync` in `ExampleRuns`.
15. **`wire`**: the snapshot's rows, by kind, made by `Rows`. `.frflow/kb.json` changes shape (derived, not read back
    by FrFlow; tools reading it must follow): every fact of DAG §4 stays, regrouped (top level: `root`, `definitions`,
    `trusted`, `vocabulary`; per node: content and hash, place with `uses` and `relies`, check with `holds` and each
    obligation's statement, the body by kind, an assumption's code), but `split`, which the split's obligations'
    statuses give. DAG §4 is rewritten in this step. Deletes `SnapNode`.
16. **`api` algebras and derived views**; `--json` output changes shape for `tree`, `show`, `inbox`, `status`, `check`
    (before and after samples listed for the owner). CLI text output identical. Deletes `LiveApi`'s 16-operation trait,
    `Overview`'s 30 counters, `NodeDetails`, the re-exports in `api/package.scala`.
17. **`cli`, `web`, `agent` on the new API; `frflow.compat` removed.** The examples' tests are rewritten in the same
    change, as munit-cats-effect suites (`CatsEffectSuite`, each test returning `IO`): `exampleResults` and `test`
    through `eval.run.Examples` and `testing.PropertyTests` in `IO`; `problems` through `Validate`; `parts`,
    `parentsOf`, `termsOf` through the `View`; `Workspace` and `LiveApi` through `FrFlowApi.inMemory`. Text and page
    behaviour identical. Deletes the old report records.
18. **Boundaries as `Boundary[T] & T`.** `val db = Boundary[Database](...)` and `db.load` unchanged in the examples.
    Deletes the `Boundary[T] => T` conversion.
19. **Remove `model` and `protocol`** once empty; tighten the architecture test to the target edges, and the size
    baseline to zero violations.

**What could change node text, Lean or decisions, and how each is kept from doing so.**

| Step | Could change | Kept by |
|---|---|---|
| 4, 5, 11 | Lean, hence check hashes, re-checks, and decided `implementation`/`model` fields (they hold Lean text) | the golden Lean of every example, byte for byte |
| 8 | contents | per-node `ref` and `hash` goldens |
| 7, 12 | signatures | every example signature verified through `Payload` |
| 12 | contents (to `V2`), code fingerprints, example sources (`idea = …`, `IDEA.md`) | review states pinned; `Formats.aligned`, `CodeNow.matches`; then the owner's `--rebind` |
| 17 | the examples' test sources | rewritten in the change that removes the facade |

**Risks.**

| Risk | Likelihood | Effect | Mitigation |
|---|---|---|---|
| a lowering differs from today's printer in a case the examples do not show | medium | a fixture's Lean moves | the fixtures' goldens too; the translation kept until both agree |
| temporary growth while `Tree/Steps` and `Expr/Prog` coexist (steps 3 to 11) | certain | about 2,500 more lines at the peak (step 8) | one representation removed per step; the size baseline allows the growth only until step 11 |
| `V1` decisions do not see an edit of `.leftOpenAbove` or a failure clause until rebound | certain for other users' ledgers | such an edit is missed | `Warning.OldForm` in `status`; the examples rebound at step 12 |
| an older FrFlow reading a ledger with `V2` contents and `tokens:` fingerprints | low | every node shows as moved | release note: no downgrade after `--rebind` |
| the macros (`Data`, `BoundaryOps`, `Source.of`, `Source.valName`) differ from today's reflection on a case the examples lack | medium | an elaboration error, or a binder named `x` | the fixtures' types and lambdas tested; errors are `ElabError`s naming the site |
| reading captures from serialized lambdas (`Captures`), as today, breaks with a Scala upgrade | low | sharing in Lean lost (`let` becomes repeated terms), Lean moves | the golden Lean catches it; the same mechanism as today |
| the run-time symbol binding of call arguments (`$argN`) is slower than today for chatty flows | low | slower `run` | `bench/` before and after step 6 |
| rewriting 5,176 lines of FrFlow tests lets a case slip | medium | a behaviour unpinned | each rewritten suite keeps its case names; a step lists cases dropped |

## 7. Rules that keep it from decaying

1. **Module graph in `build.sbt` only** (4.3). A new module or edge is an architecture change, approved first.
2. **`ArchitectureSuite`** (munit, in the `project` module's tests): scans `modules/*/src/main` imports and package
   clauses; fails on a package edge not in `project/architecture.conf`, on any package cycle within a module, on
   `private[frflow]`, and on these imports from `core`, `dsl`, `proof`, `decision`: `cats.effect`, `io.circe`,
   `java.nio.file.Files`, `scala.util.Random`, `System.getenv`, `ThreadLocal` (allow-listed: `dsl.build.Fresh`,
   `dsl.term.Values`); and on `java.util.concurrent.atomic` or `synchronized` in `eval` and `runtime` outside
   `dsl.term.Once`, `runtime.check.AssumptionWatch` and `runtime.check.Sampling`. About 150 lines.
3. **scalafix `DisableSyntax`** on `core`, `proof`, `eval`, `decision`, `dsl`: no `null` (allow-list:
   `dsl.node.Parent.of`), no `var` in classes, no `throw` (allow-list: "FrFlow bug" sites, `dsl.term.Param.value`),
   no `asInstanceOf` outside the six places of 4.11, no `isInstanceOf`.
4. **Size budgets** in CI against a committed baseline (`budget.py`): a change may not add a violation.
5. **Golden files** for every example's Lean, contents, signatures and CLI output (step 0); a change to them is listed
   in its commit message and approved.
6. **Law suites** for every instance (`checkAll` with cats-laws) and every algebra (against each interpreter).
7. **A new feature names its concept.** The pull request template asks: which of the twelve concepts it extends (or
   the theory of the new one, in two sentences), which IR case or algebra operation it adds, which interpreters handle
   it (Lean, Scala, run time, tests, content, view), which example uses it, which golden files change.
8. **Review checklist** (`.claude/skills/scala-fp/references/review-checklist.md`), plus: no analysis reads printed
   Lean or source text; no view stores what a function of `View` computes; no `Option` field that a kind decides; a
   new pattern is added to 4.10 with its example file, or not used; a name says what it is, once per concept, and a
   comment says only what the name and the types do not.

## 8. Where each problem is addressed

| Problem | Addressed by |
|---|---|
| P1 no IR | `core.expr`, `Exprs.mentions`; `Lifted` deleted (steps 3 to 6) |
| P2 string Lean | `proof.lean` AST, `Lower`, `LowerProg`, `LowerProp` over `TermTable`, `Prop`; `Scope` on types (steps 4, 5, 11) |
| P3 `Node` | `Statement` cases, edges, positions, attachments apart; interpreters out (steps 8, 9, 14) |
| P4 `KnowledgeBase` | `Theory` (5 fields), `Resolved`, `Running`, `testing.Settings` (steps 8 to 10, 14) |
| P5 core → wire | `wire` depends on the domain (steps 2, 7, 15) |
| P6 ledger on `SnapNode` | `Subject`, `Standings`, `Shown`; the regex in `Meaning.own` gone with `V2` (steps 7, 9, 12) |
| P7 cycles, visibility | top package per module, architecture test (steps 0, 2, 19) |
| P8 duplicates | one `Ty`, one `TestReport`, one `Shown`, one `OpSig`, `Walk` in core (steps 3, 7, 8, 9, 14) |
| P9 casts | `Value` literals, casts in six named places (steps 3, 6, 8) |
| P10 ambient state | `Fresh` and `Values` named and allow-listed, two memos in immutable values, `BoundaryOps` and `Data` derived and lambda names read at compile time (no registry, no Java reflection on types), explicit `Env`, `Hits`, config read once (steps 6, 8, 13, 14) |
| P11 raw-text content | `Content` with forms; `V2` without source text; `ScalaTokens`, `Governance`, `RelPath`; `--rebind` for existing decisions (steps 7, 8, 12) |
| P12 flattened views | `NodeView` by concept, `Placement` by relation, `Tally`, the snapshot by kind (steps 15, 16) |
| P13 thrown model errors | `Fault`, `ElabError`, `Problem`, `ValidatedNec` (steps 8, 10) |
| P14 effects | algebras with in-memory interpreters (step 13) |
| P15 surface width | feature audit; drops and moves (steps 1, 14, 18) |
| P16 golden only on fixtures | step 0 |
| P17 two statements of the purpose | `IDEA.md` removed, `README.md` ordinary prose (step 12) |

P11 is addressed for the content only once `V2` is in use: until a ledger is rebound, its `V1` decisions are compared
on the common fields, and their code by raw text.

## 9. Changes in this revision

Revision 6 answers the round-5 review (`r43-review-5.md`). The planned code compiles with `-Werror` and its 33 tests
pass (`sbt compile proof/test decision/test dsl/test project/test evaluation/test runtime/test`).

| Finding | What changed |
|---|---|
| R5.1 (major) adapters not wired | `Running.operations` wires every operation a plain call reaches whose node has code, the first listed, contracts and assumptions alike, as today's `opBindings` (crm's `fetch` on `recordsByQuery`, keycloak's `lookup` on `sessionLookup`); each is its service, so an adapter is checked on each of its calls. `Wiring.values` requires what the code calls (plain code's calls as attached, a define's mentions) and reports one with neither code nor a binding as `Unbound` when wired. `ServiceSuite` (with the `Search` fixture, crm's read side in small): an adapter called from a contract's code passes a good call and reports, then throws, a seeded wrong result (`Violation(RecordsByQuery, Post, …)`); without an adapter, wiring gives `Unbound(SearchReturnsQuery, List(fetch))`. 4.3. |
| R5.2 mutable state named | The running system's shared mutable state is named as two kinds, the watch's cell and the samplers' counters, in `AssumptionWatch`'s and `Sampling`'s docs, 4.1, 4.3 and 4.8.B; the architecture test (7, rule 2) allow-lists atomics and locks in `eval` and `runtime` only in `Once`, `AssumptionWatch` and `Sampling`. |
| R5.3 examples' givens at wiring | What must be bound is today's `needed`: `Wiring.needed` adds `Statement.givens` (the symbols the contract's examples give values to) to what its promise reads and its code calls. |
| R5.4 code-only symbol typed `Unit` | `Givens` takes `typeOf: SymbolName => Option[Ty]`; data or a table given for a code-only symbol is `Problem.DataForCodeOnly`, reported by `Validate` with every other structure problem (before anything runs; `Supply.literal`), so `Givens` meets it only as a FrFlow bug. |

Revision 5 answered round 4 (R4.1–R4.6): `enforce` and `checkExamples` written as small functions (`Service`,
`Guard`, `CallValues`, `AssumptionWatch`, `Sampling`, `CallCheck`, `Kept`, `Givens`, `Assumes`, `PromiseExamples`,
`CodeExamples`) with their tests; the mechanical rule as today's, through `ReadProof` and `Unproven`; `Rows` writing
each case itself; `Promise.withExamples` and the contract instances in `OnContract`'s companion; both problems of an
exemption; `VocabularySuite` pointing at step 0's golden.

Revision 4 answered round 3 (R3.1–R3.14): `Texts.vocabulary` as today's field, pinned against auth's ledger; the
failure clause's post in a flow contract's claim terms; `examples` on assumptions about an operation over
`OnPromise`, `leftOpenAbove` over `OnContract`; `TermTable` computed once and passed on; every flow the developer's
code builds in a `Fresh` scope; `Obligation.doc` made where the obligation is; `CallShape` and `DefineShape`; the
snapshot as `wire`'s own rows with one mapping; `split` left out of the snapshot; `LowerProp.evaluates` reading the
`Value`; `NotAllowed.LemmaImport`; the invariant problems; `Forall(about, body)`.

Revision 3 answered round 2 (R2.1–R2.23): the node views filled in by concept and the snapshot by kind; `LowerProp`,
`TermTable`, the invariant scope on types, the `V2` contents and the subjects written, with `impl` and `unsat` lowered
from `Prop` byte for byte; today's proof-file rules, one case each; a design's parents in its own meaning; one error
shape (`Fault` placed as `ElabError`); shared lowering helpers; no budget wrappers; one naming convention and one name
per concept; one flow interpreter, sequential or concurrent; typed run-time terms; named state; defines named at
compile time and declarations kept for `Validate`; the rule gaps closed; steps 12 and 13 merged.

Revision 2 answered round 1 (R1.1–R1.26) and applied the owner's changes: `IDEA.md` removed as a concept, the README
ordinary prose, no numbered questions, old `IDEA` entries read and kept by `Retired`; the plain-code path placed in
the module graph; production flows run directly; a Lean AST reproducing crm's files; obligations with `Iff` and
evaluations as an input; `Shown` per piece; flow and function contracts and examples apart; signatures over today's
payload; a layout-keeping fingerprint with `confirm --rebind`; review with rewording; a rule per command; streamed
checks; views without `Analysis`; the readability rules (short definitions, few patterns, short comments).

Revision 1: first full version (architecture map, sources, target with planned core code, feature audit, plan,
rules).
