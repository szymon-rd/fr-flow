# r43 appendix: feature audit

Every user-visible feature and DSL operation, the concept it belongs to in the target (section 4 of
`r43-architecture.md`), where the examples use it, and a proposal. The owner decides; "drop candidate" means no example
and no doc workflow needs it, so it can go without changing what any example proves or decides.

Use counts are occurrences in `examples/*/src` (auth, keycloak, crm, sharing), measured with grep on fbea98d and
checked on 3aa8cd7 (only `README.md` changed between them). "tests
only" means only FrFlow's own suites use it.

## The DSL: vocabulary and terms (concept: Vocabulary, Expr)

| Feature | Target concept | auth / keycloak / crm / sharing | Proposal | Reason |
|---|---|---|---|---|
| `Opaque(name, means)`, `User.T` | `vocab.Sort` | all | keep | the root speaks in open types |
| `Param[T](name, means)` (fact or operation) | `vocab.Symbol` | all | keep | operation-ness is derived, not declared |
| `Param` without a Lean type (code-only) | `SymbolType.CodeOnly` | crm, sharing (connections) | keep | now a case, not `LeanType.unknown` |
| `define { … }` (0 to 6 inputs) | `vocab.Define`; `dsl.shape.Defines.define`, named as its val at compile time | 0 / 18 / 30 / 58 | keep | |
| `object X extends Data[X]` | `LeanType` derivation (`DataMacros`) | 1 / 4 / 13 / 23 | keep | |
| `LeanType.product[T]`, `LeanType.sum[T]` (a type kept apart from its terms) | the same derivation, without the term constructor | sharing 8 + 5 | keep | |
| `===`, `=!=`, `&&`, `\|\|`, `!`, `==>` | `Expr.Prim` | all | keep | |
| `forall`, `exists` | `Expr.Quant` | 4+2 / 14+2 / 17 / 37 | keep | |
| `.on[Case]` match | `Expr.Match` | 0 / 12 / 29 / 98 | keep | |
| `c.fold(a, b)`, `o.fold(z)(f)` | `Expr.If`, `Expr.Match` | 0 / 9 / 8 / 73 | keep | |
| `let(v)(x => …)` | `Expr.Let` | sharing 5 | keep | |
| list, option, map, set operations | `PrimOp` (one per meaning, the operand's type telling the container), `Iterate` (every operation with a body), `Fold` | all | keep | |
| `BigInt` arithmetic; `Int`/`Long` compare only | `NumKind` | all | keep | |
| `p.value`, `d.fn` in plain code | `dsl.term.Values` (`Param.value`), `eval.DefSyntax` with `Def.compiled` | value 25, fn 8 (main) | keep | |

## The DSL: nodes (concept: Statement, Edge)

| Feature | Target | Use | Proposal | Reason |
|---|---|---|---|---|
| `Node.claim` (root: no parents) | `Statement.Claim` | 4 / 10 / 7 / 12 | keep | |
| `Node.invariant` + `.keeps` / `.exempt` | `Statement.Invariant`, `Edge.Keeps`, `Edge.Exempt` | 0 / 1 / 1 / 0; keeps 0/1/2/0, exempt 0/2/8/0 | keep | keycloak and crm use them |
| `Node.contract(op)` | `Statement.Contract` (a function) or `FlowContract` (a flow), by the operation's type | 1 / 2 / 6 / 29 | keep | |
| `Node.assumption(id, …)(formula)` | `Statement.Fact` | keycloak, sharing | keep | |
| `Node.assumption(op)(…)(post)`, with `.examples` | `Statement.AssumedCall`; `examples` over `OnPromise`, run against the promise and the adapter | keycloak, crm (examples: crm 2, keycloak 2) | keep | |
| `Node.assumption(boundary)(Model)` | `Statement.Model` | crm 1, sharing 4 | keep | |
| `Node.definition(…)(T := of[X], p := …)` | `Statement.Definition`, `Fixing` | 4 / 5 / 5 / 9 | keep | |
| `Node.design(…)(files*)` | `Statement.Design` (`NonEmptyList[RelPath]`) | 1 / 2 / 4 / 3 | keep | |
| `.under(parents*)` | `Edge.PartOf` | all | keep | |
| `.replaces(other)` | `Edge.Replaces` | none | keep, review later | documented as how alternatives are proposed; the agent's workflow uses it |
| two definitions of one term as alternatives | `analysis.Choice` | none in examples | keep | same mechanism as `replaces`; tests cover it |
| `idea = "Section"`, `KnowledgeBase(…, idea = …)` | none | 77 arguments, all four | remove (owner) | `IDEA.md` is no longer a FrFlow concept; contents in `V2` do not hold it, so removing it moves no decision |
| `.examples(bindings*)(expect/reject…)` | `Promise[CallExample]`, `Promise[RunExample]` | 1 / 4 / 10 / 29 | keep | |
| `bind`, `bindTable` | `example.Given`, `Supply` | bind all; bindTable auth 1 | keep `bindTable` only if Lean evaluation of function-valued givens is wanted | one use; it exists so Lean evaluates the example |
| `.expects(statement)(consequence)` | `Claim.expects` | crm 4 | keep | proves expected consequences of the root |
| `.checkedBy(check)` | `Promise.check` | keycloak 1, crm 4 | keep | |
| `.checkedAtRunTime(RunCheck)` | `code.Attachment.runCheck` | none (tests only) | merge into the attachment; drop candidate | no example chooses a policy; the default per code state covers all |
| `.leftOpenAbove` | `reliance = LeftOpen`; a `V2` content field; one extension over `OnContract` for both contract cases | sharing 5 | keep | |
| `.failsChangingNothing[E]`, `.onFailure[E]` | `FlowContract.failure: FailureClause`; a `V2` content field | sharing 2 / 1 | keep | |
| `.checkedAgainst(holding, readBack)`, `.implementedBy(holding, readBack)` | `CodeTable.realized` (`Realizes.Outside`, `Own`); shown per realization in `Shown` | crm 1+2, sharing 1+3 | keep | |

## The DSL: code and running (concept: Code, runtime, testing)

| Feature | Target | Use | Proposal | Reason |
|---|---|---|---|---|
| `kb.implement(c, calls*)(code)` | `Code.Tested` | 3 / 2 / 3 / 1 | keep | |
| `kb.implementProven(c)(define)` | `Code.Proven` | keycloak, crm, sharing | keep | |
| `implementProven(c)(define, runs)` | `Code.ProvenBeside` | crm | keep | |
| `implementProven(job)(flow)` | `Code.ProvenFlow` | crm, sharing | keep | |
| `kb.service(c)(bindings*)` | `runtime.Running.service` (facade syntax) | 2 / 4 / 10 / 22 | keep | moved out of the DSL type, same user syntax |
| `kb.run[F](contract)(bound*)` | `eval.run.FlowRun.sequential` (as today); `FlowRun.concurrent` for the interleavings tests | crm 2, sharing 3 | keep | |
| `kb.reporting(v => …)` | `runtime.Reporter` (argument of `Running.make`) | none (tests only) | move to runtime; keep | an application needs a sink; it is run-time configuration (rule B5) |
| `kb.generating(gen)`, `Gen.derived`, `.describedAs` | `example.Gen` (data, made by `dsl.term.Gens`) + `testing.Draw` | crm 1, sharing 12 | keep | |
| `kb.testedWith(TestSettings)` | `testing.Settings` from `project.Config` | none (tests only) | move to config; drop from the DSL | how tests run is the checker's configuration; `FRFLOW_SEED` already overrides it |
| `FRFLOW_SEED=fresh` | `project.Config` | CI doc | keep | |

## The DSL: flows (concept: Prog)

| Feature | Target | Use | Proposal | Reason |
|---|---|---|---|---|
| `for`/`flatMap`/`map`, `Flow.pure`, `*>`, `as`, `void` | `Prog.Bind`, `Pure` | crm, sharing | keep | |
| `<*`, `flatTap`, `product`, `tupled`, `Flow.sequence` (USAGE, "Effectful code") | `Prog.Bind`, `Let`; `Collect` for `sequence` | tests only (auth's `flatTap` is on `IO`) | keep | each is two lines over `flatMap`; documented |
| `Boundary[T]`, `Boundary.failing` | `vocab.BoundarySig` | crm 1, sharing 1+2 | keep | the proxy becomes `Boundary[T] & T`: no implicit conversion |
| `StateModel[S]`, `state.get/set/update` | `vocab.StateModel`, `Prog.Read/Write/Modify` | crm 1, sharing 2 | keep | |
| `traverse_`, `traverse` | `Prog.Loop`, `Collect` | crm, sharing | keep | |
| `foldM` | `Prog.Accumulate` | tests only | keep | small, completes the Traverse vocabulary |
| `c.foldF`, `Flow.whenA/unlessA`, `Flow.ifM` | `Prog.Branch` | whenA sharing 3; others tests only | merge into one `Branch` surface (`whenA` plus `foldF`); drop `ifM` candidate | `ifM` is `flatMap` + `foldF` |
| `raiseError`, `handleErrorWith` | `Prog.Raise`, `Catch` | tests only | keep | needed by `attempt` and `retry` |
| `attempt` | `Prog.Catch` | sharing 7 | keep | |
| `retry(Schedule)` | `Catch` + clock | sharing 1 | keep | |
| `guarantee`, `Flow.bracket` | `Prog.Guard` | tests only | drop candidate | no example; adds a concurrent step with its own reading |
| `timeout(d)` | clock readings | tests only | drop candidate | no example; easy to write with `Flow.now` |
| `parTupled` | `Prog.Par(left, a, right, b)` + `commute_i` | tests only | drop candidate, or keep with `parTraverse` | `parTraverse` covers the example's need |
| `parTraverse`, `parTraverseN` | `Prog.ParEach` + `commute_i` | sharing 3 | keep | |
| `race` + `Races` boundary | `Prog.Race` | tests only | drop candidate | no example; its reading (a scheduler boundary) is the most intricate step |
| `atomically` | `Prog.Atomic` | sharing 5 | keep | |
| `Flow.now`, `Flow.sleep`, `waitUntil`, `Clock`, `ClockModel`, `FakeClock`, `SystemClock` | clock boundary | now sharing 2, FakeClock 13, SystemClock 3; sleep, waitUntil tests only | keep the clock; `sleep`/`waitUntil` keep (used by `retry` and `every`) | |
| `Flow.every(period)(job)` `.once/.runs/.schedule` | scheduler | sharing 2 (+ schedule 3) | keep | |
| `Flow.effect(x)(f)` | DSL `Flow.Effect(args, run, result)` only (never in `Prog`), run by `FlowInterpreter` with its terms' values | crm 9, sharing 5 | keep | production implementations |
| `FaultPlan`, `World(…)`, `Failed(…)` in examples | `RunExample.before`, `RunEnd.Fails` | crm 10, sharing 3+8 | keep | |

## Checks Lean makes (concept: Obligation)

| Obligation | Target | Proposal | Reason |
|---|---|---|---|
| `complete`, `holds`, `root_impl`, `impl` | `Prop.Implies` over `ClaimOf` | keep | the method |
| `needed_C`, `vacuous`, `restates`, `clash`, `unsat` (tries) | `TryKind` | keep | they catch splits that say nothing or contradict |
| `restates_i_C` | `Prop.Iff` with `ConjunctOf`, from `Exprs.conjuncts` | keep | |
| `idle` (root) | `Substitute.Nothing` | keep | guards the "exactly" of the root |
| `feasible` | `ObligationName.Feasible` | keep | guards authored proofs |
| `check`, `cover_X`, `expect_i` | as names | keep | |
| `eval_i`, `probe_j` (Lean vs Scala) | `Prop.Evaluates(Evaluation)`, the values from `eval.Reflect` | keep | the cross-check of the two denotations |
| `commute_i` | `Prop.Commutes` | keep with `parTraverse` | |
| authored proofs, `scaffold`, proof rules (today's `forbidden` list and allow-lists: no `admit`, `native_decide`, `implemented_by`, metaprograms, other options, attributes, other imports; axioms audited) | `Discharge.Authored`, `proof.reading` (`ProofRules`, one `NotAllowed` case per rule) | keep | |

## Tests and run time (concept: testing, runtime)

| Feature | Target | Proposal |
|---|---|---|
| property tests of tested code (derived generators, seeded by examples, shrinking, coverage, counterexamples replayed, `.frflow/tests.json` cache) | `testing.PropertyTests`, `Hits`, `TestReport` | keep |
| model tests of `implementedBy`/`checkedAgainst` (generated runs, shrinking) | `testing` | keep |
| fault sweep, interleavings in IO | `testing.Interleavings[F[_]: Async: Random]` | keep with `parTraverse` |
| `service`: every call / none / sampled; assumptions on change; `Violation` then `ContractViolation` | `runtime` | keep; `Sampled` only if `checkedAtRunTime` stays |

## Decisions and review (concept: Content, Ledger, review)

| Feature | Target | Proposal |
|---|---|---|
| accept / reject / confirm / revisit / gone, `-m`, `--yes`, `--revisit` | `review.Decide` | keep |
| causes self/above/parts/code/revisit/merged | `review.Cause` | keep |
| rewording a formal node reviews only it (`reworded`) | `review.Reworded`, read by `Standings` | keep |
| mechanical batch | `rules.Accepting.mechanical` | keep |
| refusals (moved since seen, short reason, not a proposal) | `review.Refusal` | keep |
| signed decisions, keys filed in `.frflow/keys` | `ledger.Payload` (today's payload), `Seals`, `port.KeyRing` | keep; every recorded signature verifies |
| ledger file with contents and values deduplicated | `wire` codec of `Ledger` | keep the format |
| `IDEA.md` decided (`accept IDEA`), sections named by nodes, `From:` lines, Not modelled, idea warnings | none; old `IDEA` entries read and kept by `ledger.Retired` | remove (owner); the examples get a `README.md` |
| code cause from governed files | `CodeFingerprint.Tokens` (comments ignored, lines and indentation kept) | change: comments and spacing no longer move decisions, once rebound |
| `confirm --rebind` (new) | `Decide.Rebind`, `rules.Rebinding` | add: the one signed step moving decisions to `V2` and `Tokens` |
| held aside by a layer | `Views.inbox(aside)` | keep |

## Front ends

| Feature | Target | Proposal |
|---|---|---|
| `tree`, `show [--full]`, `diff`, `inbox`, `find`, `review` (interactive), `render`, `check [NODE]`, `scaffold`, `status`, `ci`, `--json`, `--plain`, exit codes | `cli` over `api.Reading/Deciding/Proving` | keep |
| web view (`serve`, token, graph, node, diff, inbox, decide, stale-model guard) | `web` over the same algebras | keep |
| `CliExtension` (commands, `Contribution`), `WebExtension` (routes, script) | `api.Extension` | keep; `Contribution`'s `Style => List[String]` fields become data rendered by the CLI |
| `frflowInit`, `frflowInitAgent` | `cli.Init`, `agent.Init` | keep; the empty knowledge base has no `idea`; the agent writes a README draft and proposes the root |
| agent layer: `said`, `asked`, `replied`, `conversation`, `ask`, `close`, `answer`, `context`, `[?]` in review, web panel | `agent` over `api` | keep; rebuilt on `api` (step 18); questions have no numbers: `replied` names a question by its words |
| `ask --idea TEXT`, `IdeaSources` (`From:` lines against questions) | none | remove (owner) |
| `bench/` scale project | tooling | keep |
| `.frflow/kb.json` (DAG §4) | `wire.snapshot` rows, made by `Rows` | tools | keep every fact, regrouped by kind; drop `split` (the split's obligations' statuses give it) | the codecs are `wire`'s own rows', not the domain's |
| `examples/rebac` | none | not a candidate: untracked derived output (`.frflow/*.json` under a gitignored rule); nothing in the repository |

## Summary of candidates for the owner

Drop candidates (no example uses them): `race` with `Races`, `guarantee`/`bracket`, `timeout`, `parTupled`,
`Flow.ifM`. Move: `checkedAtRunTime` to the code attachment (or drop), `testedWith` to the checker's configuration,
`reporting` to `runtime`. Removed at the owner's request: `IDEA.md` (`idea = …`, `accept IDEA`, sections, `From:`
lines, `ask --idea`) and numbered questions. Added: `confirm --rebind`. Change in behaviour: comment-only and spacing
edits of governed files no longer bring nodes back, once a ledger is rebound.
