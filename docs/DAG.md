# FrFlow on a DAG of refinements: the design

This file is the design every change follows, in brief; [redesign/ARCHITECTURE.md](redesign/ARCHITECTURE.md) is the
full record, and [redesign/owner-decisions.md](redesign/owner-decisions.md) the owner's decisions it applies (§n
below). Where code and these disagree, they win; a change that needs to depart from them says so in its commit message
and in them.

## 0. Principles

1. **A small set of roots.** A FrModel has one or a few root statements, on any of its Definitions and Declarations
   and relating them too, kept concise by its author: each states one idea, and together they are the purpose (§11).
   A root is stated as *exactly* (what users can do and what must never happen, together), so that a system that
   does nothing does not meet it; the `idle` try asks it of the roots together. Where the purpose is more general
   than the code, it is stated over Declarations, and claims at the bottom say what each is in terms of the code
   (rooms' `bookedAfterIsStored`).
2. **A graph of refinements.** Every other node refines the nodes above it, and may refine several, so the nodes form
   a directed acyclic graph. Every step is proven, every node is decided: a model of why the system is as it is.
3. **Granular and understandable.** One node says one thing, in the developer's domain words, in one sentence; no
   concepts glued with `&&` (a style guide, not a check: §10, §16). A node that only restates its part is reported
   (`restates`). A parent should have 2 to 5 parts. The first split is ⇒/⇐ (safety and capability) or state/reads,
   not one part per conjunct.
4. **Domain-driven.** The roots speak in the most general terms; nodes below introduce the domain's concepts as they
   are needed. Each value has one meaning, written in words (`means`), and is given its meaning once.
5. **Proofs are central.** Every step is a Lean theorem; the code at the leaves is proven where it is written in the
   DSL, and tested where it is plain Scala; what is trusted is a named, visible list of assumptions. Nothing is
   checked when the code runs (§2): FrFlow is for testing before production and strict static guarantees.

## 0a. The core concepts

Three kinds of nodes, two kinds of values, two quantifiers (§15); nothing else, under any name.

- **Nodes.** `Node.claim(statement)(formula)`: proven from its parts or of the code it mentions, or tested where the
  code is plain Scala. `Node.assumption(statement)(formula)`: trusted, the developer's decision: the world outside the
  code (what a model's state starts in, that only the code changes it, that runs on it never interleave, a
  schedule), an outside system's promise, what values from outside meet. `Node.design(statement)(files*)`: a decision
  about code no proof covers.
- **Values.** `Declaration[A](means)`: abstract, known only through the statements about it; no code, define or
  program uses it, nothing implements it. `Definition[A](means)`: of any type, what code and programs use; it must get
  a meaning (§15). `define { … }` and `program { … }` are Definitions given their meaning on the spot.
- **Quantifiers.** `forall` is every possible value. `always` is every value the code FrFlow covers can produce
  (§19): `always[T](x => …)` every value of `T` that can be made, a hypothesis of every statement about such values
  wherever they are held, met wherever covered code makes one; `always(stored)(s => …)` every state a model reaches,
  kept by every program writing it, from a start that meets it. Values from outside are covered by an assumption of
  `always` on their type (§21): statements are about values, not about a function's inputs.
- **Edges.** `.refines(parent)` makes a node a part, or, for a claim of `always`, a rule below the statement it
  serves (no part of the step); `.assuming(assumption)` a premise; `.replaces(other)` an alternative.
- **The World** (§33, §41, §43): the application at one moment, one field per model's state. A statement holds in
  every reachable world and never names it: what changes is read in the current one (`stored.current`), a program's
  run is `p(x).result` and `p(x).after`, and `.current` names the world before a run where a statement reads one.
  `t.isConstant` says no run changes `t` (§44, §45 A).

## 1. Vocabulary

- A domain type is a case class or an enum deriving `LeanType`: a Lean `structure` or `inductive`.
- A Declaration may change with the World: Lean takes it as a function of the world where a statement reads it
  beside something that changes, and as a value otherwise. A rule (`always`) may not read one that changes (§45 C).
- A Definition gets its meaning once: in the FrModel (`implementProven`, `implementTested`, `implementValue`,
  `implementProvided`), on the spot (`define`, `program`), or from a `StateModel` for an operation on a state.
  `check` refuses one nothing defines, one defined twice, and code using a Declaration.
- A define changes with the World exactly when its body reads state; it then takes the world last and is read in its
  caller's world, or in the one it names (`ofRoom(room).in(w)`).
- Names come from the `val`s: a node's id is its val's name, a Definition's and a Declaration's too. Renaming a val
  renames the node: a new node to decide (`.replaces(old)` links them).

## 1a. Programs and state models

- **A program** is one type, `Flow[R]` (§42), written as a `for` comprehension; `A => Flow[R]` is a Definition's
  type. Its steps are recorded once: Lean reads them, the Scala tests run them on the models, production folds them
  into `F: Async` (`knowledge.running[F](…)`). Every combinator is kept: `atomically`, `when`, `cond`, `ifM`, `each`,
  `collect`, `fold`, `parCollect(N)`, `parTupled`, `race`, `raise`, `handle`, `attempt`, `guarantee`, `bracket`,
  `timeout`, `retry`.
- **There is no boundary** (§36): what FrFlow cannot see is a Definition given plain Scala, whether it is the
  project's code or calls an outside system. An operation on a state gets its meaning in Lean from a `StateModel`
  (`inRoom.means(…)`, `add.means(…)` over `state`), its plain Scala tested against the model on generated runs. An
  operation known only by assumptions (`fetch.assumed`) is an unknown function of its model's state, its assumptions
  hypotheses, its Scala tested against them where it can be.
- **What the world outside does** is said of the model: `onlyCodeChanges`, `initially(s => …)`, `atomic` (§31,
  §32, §36), and of the clock `schedule`. Which programs change a state is derived from the code (§31).
- **A failing program** declares its error on its Definition, `.failsWith[E]` (§45 B, §46); its `result` is then an
  `Either[E, R]`, and FrFlow checks the declaration against the code.
- **Time** (§47) is Cats Effect's: the clock is FrFlow's model (`Clock.now`, `Clock.sleep`, the world's own
  `elapse`), steps of code take no time, the world moves the time on between runs and at each of the clock's steps,
  waits at once take the longest of them; every rule and `isConstant` reading the clock survives time passing.
- **Concurrency.** Steps at once are read in turn and proven to commute where they touch a model in common
  (`commute_<i>`), so the reading stands for every interleaving.

## 1b. Proven, tested, assumed

- **Proven**: a `define` or a `program`, of which Lean proves the claims mentioning it.
- **Tested**: plain Scala, tested against the claims mentioning it on generated cases (each argument drawn meeting
  the rules on its type), or, for a model's operations, against the model on generated runs, two calls at once
  among them.
- **Assumed**: what an assumption says, trusted; plain Scala known only by assumptions is tested against them where
  a generated run can evaluate them, and "trusted, not tested" otherwise.

What proven code hands to plain Scala meets the rules on its type (`made_<code>_call_<i>`, §37): a proof only.

## 2. Nodes

- A claim with parts is proven from them: its parts, with the assumptions it lists, imply it (`complete`), each is
  needed (`needed_<part>`). Its rules (claims of `always` below it) are no part of the step.
- A claim mentioning proven code is proven of the code (`impl`), its parts or the claims about what the code calls
  as hypotheses. A claim at the bottom mentioning a Declaration says what the Declaration is: it is never asked
  `impl`, and the proven code stands in it in its consistency group (§3a).
- A claim mentioning plain Scala is tested against it: read as a call where it applies the Definition to exactly its
  leading `forall` variables, the whole formula evaluated otherwise; one with no Scala value is not checked, and
  `status` warns when nothing else checks it.
- An assumption is trusted, and listed by every check resting on it (`.assuming`), which FrFlow derives and checks:
  a missing premise or one not needed is refused.
- A design node governs files; a change to them brings it back. Every source file is governed by one node (an
  implementation, or a design).
- At least one root, never an assumption; no cycle over parts and premises; edges inside the model.

## 3. Lean obligations

What Lean is asked of each node is a function of the resolved theory (`proof.audit.Obligations`). Generated Lean
is under `lean/FrFlowGen/<Model>/` (a module per node, its `Spec` and its `Checks`, the models, the domain);
developers' proofs under `lean/Proofs/<Model>/`.

| Obligation | Asked of |
|---|---|
| `complete`, `needed_<part>` | a claim with parts |
| `impl` | a claim mentioning proven code |
| `root_impl` | the roots, of the code, through the claims saying what each Declaration is |
| `cover_<program>` | each program writing a store an `always` is about; `cover_elapse` where it reads the clock |
| `made_<maker>` | each proven define, program or operation making a value an `always[T]` is about |
| `made_<code>_call_<i>` | each call from proven code to plain Scala, of the arguments' rules |
| `start_<node>` | an `always` about a store, from what `initially` says |
| `outside` | a claim of `always[T]` whose `T`s come from outside |
| `commute_<i>` | each two steps at once that touch a model in common |
| `consistent_<i>`, `inhabited_<node>`, `satisfiable_<i>_<node>` | §3a |
| `example_<set>_<i>` | §3b |

The tries (`vacuous`, `restates`, `clash`, `unsat`, `idle`, `frozen`) are refuters, reported as shown or not shown. A
step refuted carries the case Lean confirms. A rule is kept only as every rule its obligations take is: a statement is
open while a rule it takes is open, for any reason (its `cover_`, its `made_`, its tests, nothing meeting it).

## 3a. Consistency and vacuity

- **Consistency** (§15, §18, §28): the statements at the bottom and the assumptions beside them, in groups sharing an
  open value, each `consistent_<i>`: some meaning of every open value makes them all hold. Witnesses are derived where
  possible (an equation, a bound, a fixed value, proven code, solved in order); a group FrFlow cannot witness is
  proven by hand (§39). A group not proven is a failure, not a warning: the whole model's proof is red, and so is
  every statement proven from parts over a Declaration while a group below it is not proven. Tested Scala alone is
  evidence, not proof.
- **Vacuity**: positive statements guard against a model that says nothing (a root stated as *exactly*), and two
  small proofs: `inhabited_<node>`, some value meets an `always` (with every other `always` on its type), and
  `satisfiable_<i>_<node>`, each condition `A` of `A implies B` can hold. Witnesses come from the generators or a
  search of small values. Reported, not gated.

## 3b. Examples written as tests

Examples are ordinary tests (`class GrantedExamples extends FrFlowExamples(rooms)`, `example(name): fact`), read by
`check`, evaluated against the code and in Lean against the claims (`example_<set>_<i>`, the `i`th of its class). Nothing depends on them (§18): the
theory and its Lean are the same without them. An example whose values break a rule on their type is refused.

## 4. Snapshot (`.frflow/kb.json`), per node

An export for tools, in decision order; FrFlow never reads it back.

- `header`: `id`, `kind` (`claim`, `assumption`, `design`), the content as decided and its `hash`, what a decision
  binds.
- `place`: `parents`, `parts`, `assumes`, `relies` (the claims about what its code calls), `keptBy` (the programs
  keeping a rule).
- `check`: `status`, `holds`, and its `obligations`, each with its name, status and Lean's detail.
- `body`: for a claim or an assumption (`stated`), how it is checked, the call it reads as, its code and its tests
  (cases, against what, seed); for a design, the files it `governs`.
- Top level: `kb`, `roots`, `trusted` (what the roots rest on), the vocabulary (each value and what it means),
  `consistency` (each group: its statements, open and provided values, status), and the examples as checked.

A node's content is its fields as decided: `kind`, `parents`, `parts` (a claim's), `assumes`, `statement`, `formula`
(the canonical print of the elaborated formula, what a decision binds), `written` (the source, for display),
`vocabulary`, and for code `checking`, `writers`, `governs`, `call`, `replaces`, `reliance`, `failure`,
`implementation`, `model`.

## 5. Decisions

- A node is decided once, whatever the number of its parents; its decided content is its content (§4).
- **Causes.** `self`: what it says changed. `parts`: its list of parts. `above`: the meaning of what it rests on
  (its parents, the values it uses, the claims its code relies on), each with its own chain; a node's meaning has no
  parts, so a new sibling reviews the parent only, and a change above a diamond moves the shared node once. `code`:
  the code it governs. `revisit`: the developer asked. `merged`: two decisions following the same one (two
  branches). `writers`: a new program started changing a store its rule is about (§31).
- **Review follows meaning.** Rewording a node with what Lean reads unchanged reviews that node and not what rests
  on it. Any change of meaning cascades.
- **Accepting** a node whose own content did not change is a `confirm`: the reason it was chosen stays. Accepting a
  change acts on what rests on it, each once, parents first; those named with `--revisit` are revisited, those that
  moved only with it confirmed.
- **Mechanical**: a node under review whose own content did not change, that Lean proves again, its examples
  passing. The mechanical batch is one decision (`confirm`).
- **Order.** A node waits for the first node it rests on that is not accepted: a parent, a premise, a value it uses.
- **Alternatives** are `replaces`; accepting one rejects the other.
- **Refused**: a decision on a node that moved since the developer saw it, a reason of fewer than three words, code
  failing a generated case or not tested since it moved, a decider not listed, a ledger whose committed history was
  rewritten.
- **Who decides** (§2): `.frflow/deciders`, committed and signed by a listed key, names the keys whose decisions
  count. The ledger holds, per node, its decisions in order, each with the content it binds, the reason, the
  alternatives rejected, the commit, the decision it follows and its signature; a node's committed history must be
  a prefix of the working one, or nothing of it counts until a listed decider runs `rebase` (`.frflow/ledger-base`).
- **Held aside.** A layer on top may hold a node out of the developer's queue (while it is asked of the agent); the
  inbox lists it apart, and nothing else about it changes.

## 6. Reading a node, and where a change belongs

`show --full NODE` gives what bears on a node: its statement and formula, why it was accepted, how it is checked,
where it sits, its parts and the rules it uses, what moved, and its obligations in Lean. `find` names the nodes that
govern a file, or mention some words. A new statement belongs under the lowest nodes it helps prove, as a part; never
as a restatement. A rejection's reason that asks for something is answered by a node in its place. `scaffold` writes
proof stubs for what the last check left open; `check` prints the goal Lean leaves when automation gives up.

The developer's flow is in the CLI. The `web` module serves it in a browser (the sbt task
`sbt "PROJECT/serve --as NAME"`, not a CLI command) over the same API, so a decision is recorded alike from either.
Both take layers on top (`Extension`: a `CliExtension`'s commands and what it adds to a view; a `WebExtension`'s
routes and script); the core depends on none. The AI agent's layer is one, described in
[USAGE.md](USAGE.md#with-an-ai-agent).
