# The owner's decisions

The owner's decisions, recorded as he gave them during the design; `ARCHITECTURE.md` applies them, and its Appendix A
says where each is applied. "§n" is a section of this file. "§4.8", "the feature audit" and "revision n" in the text
are those of the design's revision log, `history/ARCHITECTURE-r15-log.md`; the feature audit is `features.md`.

## 1. No IDEA.md; the README is just a README
The owner: "IDEA.md is weird btw. It is unstructured. I don't think we should have that. The notion of questions (Q1,
Q2, etc.) being referenced to without clear definition, the same. README is what it should be tbh, just that."

- Remove IDEA.md as a FrFlow concept: no idea sections, no `idea = "…"` parameter on nodes, no IDEA.md decisions
  (`IdeaDecision`, `IdeaReview`, idea-section hashing), no section-scoped review.
- A project's README.md is ordinary documentation; FrFlow neither parses nor tracks it. The decided statement of the
  purpose is the root node and its refinements.
- No numbered questions (Q1, Q2, …) anywhere: the agent's interview produces a README draft and the proposed root and
  nodes, each node with its `why`; nothing refers to question numbers. The agent layer's conversation records, if kept,
  are not referenced from files.
- Existing ledgers must still read: old idea entries are read and ignored (state how).
- The four examples get a README from their IDEA.md (content kept, the "From: Q…" lines dropped); node texts unchanged,
  so no decision comes back. Removing `idea = …` arguments from example sources must not change decided content — check
  whether ideaSection is part of the hashed content today and plan accordingly.
- Update the feature audit, the planned code, the migration plan (which step removes it, what it deletes) and the docs
  plan (docs/USAGE.md, docs/index.html, the frflow skill, `frflowInit`/`frflowInitAgent`).

## 2. Owner's decisions on §4.8 and the feature audit (after approval of revision 6)
The owner's answers, verbatim where quoted. They supersede the corresponding recommendations.

- **D. Migration: a ground-up rebuild in the same repository** ("New repo (rebuild): the same repo but grounds up").
  The step-by-step strangler with goldens is no longer required. Build the new modules from the planned core, port
  the examples onto them, delete the old modules at the end. Goldens of today's Lean are a reference, not a
  constraint: the examples' Lean may change where the new design is better.
- **Ledgers: start fresh.** "I didn't accept anything": the examples' decisions were all made by agents with a demo
  key. No `confirm --rebind`, no V1/V2 content forms, no legacy fingerprint matching; the examples get new ledgers
  decided once at the end. Old ledgers need not be read. (G is dropped.)
- **A. Terms: the user must not see tagless.** "If it needs to leak to the user then that's bad." The DSL the user
  writes stays concrete (`Term[A]`, `define`, `forall`, `Node.claim(...)`); internally an initial IR.
- **B. Ambient state: replace both scopes.** Fresh variables: numbered at compile time by the macro that reads the
  lambda (no counter, no ThreadLocal). Values in force: passed explicitly to plain code, e.g.
  `.implement(c)(env => SessionStore(env(grants), env(sessions)).decide)`. No ambient state in the DSL.
- **C. Boundaries: tagless.** `trait Database[F[_], T[_]]` (or the shape you find cleanest), with a recording
  interpreter for the proofs (the model, printed as Lean) and `IO` for production; programs over boundaries written
  `def f[F[_]: Monad](db: Database[F, …])`. The examples' boundaries are rewritten.
- **E. 13 modules**, as designed — minus `runtime`, see below.
- **F. Code fingerprint: the simple lexer** (comments stripped, lines and indentation kept).
- **No run-time checking.** "Once we are in runtime we don't care that much. FrFlow is for testing before production
  and strict static guarantees." Drop the `runtime` module and everything that exists only for it: services that
  wrap code to check each call (`enforce`/`Service`/`Guard`), sampling (`RunCheck`, `checkedAtRunTime`), the
  assumption watch, the violation reporter, `.checkedBy` (a cheaper check meant for run time), `ContractViolation` at
  run time. Code is checked by proofs and by tests before production only. Say what else this removes or simplifies.
- **Flow combinators: keep all** (`race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM`), each with tests and
  a use in an example.
- **Signing: a committed, developer-signed list of who may decide.** A decision counts only when its key is listed
  there; filing a new key under a new name is not enough.
- **Nodes have no `why`.** "Drop why." The reason for a statement is the reason given in its signed decision (the
  ledger); show it in `show`/review from there. Proposals from the agent carry their rationale in the request or
  conversation, not in the node.

## 3. README delivery rule (owner, after v7)
"Only bring to me a README that was accepted by those 3 planned reviewers as discussed."
Show or push a README only after all three cold readers (Scala dev, sceptical staff engineer, formal methods) read
that exact text and would read to the end and try it. Any edit after their review means a new reader round.

## 4. README code at a glance (owner)
"I want the code to be nice in those snippets, make sure with review agents that it is easily understandable at
glance for those actors." Before a section round, the three personas review the snippets alone
(readme-glance-brief.md) until each says every snippet reads at a glance; the section readers also answer item 10.
Library additions for this: `forall(def)`, `distinct`, `pairwise` on lists (carry into the rebuild).

## 5. Terms in tagless-final style (owner, after round 7)
"Rework architecture to use tagless final approach, especially as specified in
https://okmij.org/ftp/tagless-final/course/" (Kiselyov, Typed Tagless Final Interpreters, LNCS 7470, 2012; the course
page and its code). Supersedes the "initial IR inside" half of decision A; the user-facing half stays: the user writes
concrete `Term[A]`, `define`, `forall`, `Node.claim(...)` and never names an interpreter. See tagless-brief.md.

## 6. API forms decided for the README (owner, after glance round 4)
Change today's library now (and the rebuild uses the same forms): names from the `val` (node ids and `Param` names),
`.refines` instead of `.under`, an alphanumeric `implies` instead of `==>`, and the example forms `allows` / `forbids`
instead of `expect` / `never`. The owner authorized re-accepting the reopened nodes with the demo key, each checked to
differ only by these changes.

## 7. README showcases storage, service code and PBT (owner)
"Where is the implementation code to showcase databases / Scala code / PBT?" Decided: extend rooms now with a SQLite
store behind a boundary and its model, a `book` operation, a no-double-booking statement, and model-based PBT with the
generators shown in the README. Written in today's boundary API; rewritten for the tagless boundaries in the rebuild.

## 8. Names confirmed (owner, after round 9)
`Operation[F]` replaces `Param` for operations; `Open[A]` for open values.

## 9. Rooms root about booking; status warning (owner)
The root is the service's purpose, a statement about the `book` flow ("a room is never double-booked, and a request is
booked exactly when its room is free"), with the calendar's statements and the store's model as its parts. Small
library change in today's code; the rebuild's `Worlds.runs` does it properly. Keep the change that `status` does not
warn about examples Lean cannot evaluate only because they run plain code.

## 10. One idea per statement (owner, on the rooms example)
"Still the example you sent is bad. It has concepts concatenated together with ANDs." No statement glues concepts with
`&&`. Conditions that always hold become their own statements: invariants of a store's model state (assumed by
contracts, kept by every operation) and data invariants of domain types (checked where a value is made, a hypothesis
for every value in Lean). Applies to today's rooms example and to the rebuild's user forms.

## 11. Several roots (owner, replaces the one-root law)
"I think we could allow a couple of root nodes in general, even on a handful of operations and expressing relations
between them. One rule may be too constraining for even top level of large apps, and may not feel natural. It is up to
implementator/agent, to keep root concise." A knowledge base has a small set of root statements (claims, contracts,
invariants), on any operations, including statements relating operations. No `SeveralRoots` problem; keeping the top
concise is the author's job (the agent's skill says so).

## 12. One statement kind (owner)
"It makes sense that there is data invariant and contract on function. But isn't function also a value of higher
order? Couldn't those be expressed with one kind of node?" Decided: one statement form,
`Node.claim(subject?)(statement)(predicate)`, a refinement of its subject: no subject (proven from its parts), an
operation (its code proven or tested against it; callers assume it), a type (checked where values are made; a
hypothesis for every value in Lean; generators respect it), a store's state (every program using the store keeps it).
`Node.assumption` has the same form and is trusted (outside facts, store models). `design` stays. Contract, invariant,
model and definition stop being separate kinds (definitions are `define`). Edges: `.refines(parent)`, `.assuming(x)`.
Applies to the rebuild (revision 14) and to today's rooms example.

## 13. No subject parameter (owner, refines §12)
"Why is subject needed?" Decided: one constructor `Node.claim(statement)(formula)` (and `Node.assumption` the same,
trusted). The formula carries everything: a claim constrains every operation it mentions (code for an operation is
checked against the claims mentioning it; a claim relating two operations checks both; callers assume them); `forall`
is every possible value (proven); `always[T](x => …)` is every value of T that can be made (enforced where values are
made, a hypothesis in Lean, generators respect it); `always(store)(state => …)` is every state the store reaches (kept
by every operation using the store). Docs show forall vs always at first use.

## 14. Declaration (owner)
One concept, `Declaration[A]`, replaces `Operation[F]` and `Open[A]`: everything stated before its meaning is known, of
any type (a function, a program over a store, a plain value). The owner: "We want to have abstract concepts that do
not correspond to any actual defs down the line but are rather refined" (e.g. a top-level `authorized`). What happens
to a declaration below decides how it is checked: refined by statements only and never defined (an abstract idea,
like `authorized`); refined down to code (`granted`, `book`: `implementTested` / `implementProven`); or given a value.
The mechanism for abstract ideas (how they are characterised, whether code may use them, a witness against
contradictory statements) is not decided yet.
The owner's model of declarations: "You create declarations and then you can use them in claims and assumptions. Those
claims can build logical statements about those declarations. They can also build contracts around them. And in the
end, they can be also implemented by either a flow monad or the term API, then that is rendered to lean and proven, or
implemented by Scala code directly, and that is then verified by property-based testing." Open: how contradictory
claims about a declaration nothing implements are guarded against (the owner will answer).

## 15. The core concepts, final (owner: "three kinds of nodes + two kinds of values + forall, always")
"Those decisions are important, so make sure they are reflected in the design strictly and not worked around."
- **Three kinds of nodes:** `Node.claim(statement)(formula)` (proven, or tested where its definitions are plain
  Scala), `Node.assumption(statement)(formula)` (trusted: the outside world, a store's model), `Node.design(…)` (a
  decision about code no proof covers). Nothing else: no contract, invariant, model or definition kinds.
- **Two kinds of values:** `Declaration[A]` (abstract: used only in claims and assumptions, never called by code or a
  flow, never implemented; known only through the statements about it) and `Definition[A]` (of any type — a
  function, a program over a store, a plain value; it must get a meaning: a flow or the term API (rendered to Lean and
  proven), Scala code (verified by property-based testing), or a value; only a Definition may be used by code or a
  flow; `check` refuses a Definition nothing defines). `define { … }` is the shorthand for a Definition given its
  meaning on the spot. These replace `Param`, `Operation` and `Open`.
- **Two quantifiers:** `forall` (every possible value; proven) and `always` (`always[T](x => …)`: every value of T
  that can be made, enforced where values are made and a hypothesis in Lean; `always(store)(state => …)`: every state
  the store reaches, kept by every program using the store). A claim constrains every Definition and Declaration it
  mentions.
- **Consistency:** the statements must be proven non-contradictory: there is a meaning for every declaration under
  which every claim and assumption holds. Definitions implemented by proven code are their own witnesses; a
  witness is needed for each Declaration (usually derived from what refines it, e.g. `access === authorized` with
  `access` implemented) and for each assumption about the outside; a Definition implemented by tested Scala counts as
  evidence, not proof, and is listed so. The search for contradictions stays as an early refuter only. A knowledge
  base without a consistency proof shows "consistency not proven".
- Edges: `.refines(parent)` (a part), `.assuming(x)` (a premise). Several roots allowed (§11).

## 16. Scope of `always`, outside assumptions, the `&&` guideline (owner)
- `always` holds where FrFlow covers the code: the tree of statements (assumptions included), flows and term-API
  code, and the contract boundaries of plain Scala Definitions (their inputs and results). Values entering from
  outside are covered by assumptions about the outside world; no run-time check.
- Assumptions about the outside world are expected and "meant also to reflect the company procedures, the outside
  services, the handling of those services": e.g. only FrFlow-covered programs write the store; bookings are
  processed one at a time (one process with `atomically`, or the database serializes them); the store starts in a
  state that satisfies its `always`. These are written as assumption nodes, so they are reviewed.
- "No `&&`-glued concepts" is a style guide for the library and its agents only: no check, no warning.

## 17. Atomicity out of scope (owner)
Each program runs as one step (atomically) is assumed for now: an explicit assumption node where a proof needs it, and
a note in the README. Asynchrony (e.g. a special operator, atomicity assumed by default) is out of scope, to revisit
later.

## 18. Examples in tests; consistency and vacuity (owner)
- Examples leave the nodes. They are ordinary tests (e.g. `example("back to back: granted"): granted(List(...),
  Booking(...)) is true`), read by FrFlow and checked against the claims in Lean and against the code. They showcase
  how things work but are not central: nothing (consistency, vacuity, any rule) depends on them. `allows`/`forbids`
  and the "every contract needs a forbids" rule are removed.
- Consistency (confirmed): the bottom statements and premises (assumptions, `always` statements) are proven jointly
  satisfiable; proven steps carry it upward; split into groups sharing declarations/definitions; witnesses generated
  where possible (`f(x) === e`, bounds, proven code); "consistency not proven" is its own status.
- Vacuity: guarded by positive statements in the model (e.g. "after a booking is made, it is present in the bookings
  list"; the rooms root already says a free room's request is booked and stored) plus two small proofs: every
  `always[T]` admits at least one value, and every claim's condition (`A` in `A implies B`) is satisfiable. Witnesses
  from generators or a search; examples may serve but are not required.
