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

## 19. One word, `always`, for both forms (owner)
The owner chose to keep one word: `always[T](x => …)` and `always(stored)(s => …)` both read "every value that the
code FrFlow covers can produce" (a value of `T`, a state of the store); only how each is proven differs. The README
says so in one sentence where `always` first appears. No third quantifier word.

## 20. The architecture is approved; the rebuild starts (owner)
The owner approved this design and asked for the rebuild (section 9 of `ARCHITECTURE.md`) to start, done by agents.

## 21. Statements are about values only; no assumptions on a function's inputs (owner)
The owner: "The idea of governing input of a function is weird. We make claims on the value so far, params are the
odd one out." `outside.calls(d)` / `d.calledOnlyWith(…)` are removed. What comes from outside gets its own type, and
what is trusted about it is an assumption with `always` on that type; what the code makes from it is proven. In rooms:
`Request` (what the booking form sends) with `always[Request](r => r.start < r.end)` as an assumption, `Booking`
(what is stored) with `always[Booking](b => b.start < b.end)` as a claim, proven from it; `book` takes a `Request`.
Today's library and the rooms example follow now, not at step 11: a separate change removes `calledOnlyWith` there
and gives rooms its `Request` and `fromTheForm`.

## 22. crm's roots: the purpose is the root (owner)
The owner accepted: crm's purpose `sharedCrm` is the root; its two general expectations ("a record a user adds is
found by their searches", "nothing a user writes changes what another company finds") are root claims of their own,
proven from their own parts, not statements the purpose refines. A scenario over literal values is an example test.

## 23. README: a short core, and when a snippet passes (owner)
The owner accepted: the README shows a short core of the rooms example (its words, one root, the calendar's claim,
the calendar's code, and the bugs FrFlow catches) and links to the complete `examples/rooms`. A snippet passes when no
cold reader finds a line they cannot parse; preferences about wording do not block. `always` is defined in one
sentence where it first appears (§19).

## 24. `KnowledgeBase` is renamed `FrModel` (owner)
The owner: "Call it FrModel." The object that lists a project's statements and attaches code to its Definitions is
`FrModel` (`val rooms = FrModel("Rooms")(…)`), in today's library and in the rebuild; text that said "knowledge base"
says "FrModel". The README calls the domain types "the domain", not "the words".

## 25. Rooms keeps one type, `Booking` (owner)
The owner asked: "Can't a Booking be a Request? (So only Booking is kept)", and decided: "Use one type.", for the
README's simplicity. In rooms, `Request`, `asBooking` and `asRequest` are gone: a `Booking` is what the booking form
sends and what the table stores, and `book` takes one. What the form sends is the assumption
`always[Booking](b => b.start < b.end)` (`bookingsEndAfterStart`), which covers every booking; the claim
`endsAfterStart` is gone. The roots now list it: the purpose holds for bookings that end after they start. The general
rule of §21 stays. The cost: the assumption would also cover any later source of bookings. The library change it
needed: an `always` assumption is a rule, as an `always` claim is (a hypothesis of the statements about its type, not a
part of their step, so listing it brings no import cycle), and code storing values of its type is still proven to keep
it (`kept_by`). Every statement proven or tested whose Lean takes the rule lists the assumption; a leaf with nothing to
prove and no code (one tying a Declaration to the code) only carries it. In rooms seven nodes list it.

## 26. `generating` is called `withGenerator` (owner)
The owner: "Call it withGenerator." The FrModel method that gives a generator for a type is `withGenerator`
(`.withGenerator(roomNames.describedAs("Oak or Elm"))`), in today's library, the rebuild, the examples and the docs.

## 27. The design before step 11 (owner)
The owner approved the three changes today's library made after the design was approved, carried into the design
before rooms is ported: a claim of `always` may sit below the statement it serves (`.refines`) as a rule, no part of
the step; an assumption of `always` is a rule as such a claim is; every statement proven or tested whose Lean takes an
assumption's rule lists it, and a claim saying what a Declaration is only carries it. Rules leaving a statement's
parts is required: otherwise a rule, which Lean states as true of every value, would be a hypothesis of the step. With
them, accepted: in the rebuild nine rooms nodes list `bookingsEndAfterStart` and `neverOverlap` also lists
`tableMatchesModel`; `roomBookingsApart` keeps `noOverlap`; `start_` and `inhabited_` are asked of an `always`
assumption too (`inhabited_` stays reported); `.assuming` takes only assumptions; `show` and review list a statement's
rules apart from its parts ("Rules it uses"), so "together they make it" lists only the parts: a statement's parts
together, with the assumptions it lists, imply it, Lean proves that step and checks each part is needed. How a run is written
in a statement is decided in §34.

## 28. Consistency gates the proof (owner)
The owner: "Consistency is important, lack of it makes the proof red, warning is not enough." A consistency group not
proven is a failure, not a warning: the whole model's proof is red, and so is every statement proven from parts over a
Declaration while a group below it is not proven. This is in the rebuild only; today's library does not change (§29).
Confirmed by the owner ("Yes"): consistency counts only when Lean proves it; tested Scala alone (evidence) does not make
it proven, so auth, crm and sharing must reach proven consistency when they are ported.

## 29. Today's library is frozen (owner)
The owner: "Yup. Freeze." Today's library (`modules/*`, `examples/*` and the README's code) is frozen except for bug
fixes until step 14; every further change goes through `next/*`.

## 30. Every boundary has a model or an assumption (owner)
The owner: "Boundary must have a model or assumption." A value covered code builds and hands to a boundary is checked
through the boundary's model or an assumption about it; a boundary covered code calls with neither is refused (a
`Problem`), so nothing passes unchecked. This settles the open question of a value handed to a boundary with no model.
Confirmed by the owner ("Yes"): the values a program passes to a boundary must meet the `always` rules on their type
(a `made_` at the call).
Superseded in part by §36: there is no boundary; every Definition has a meaning, and `made_` at the call is §37.

## 31. `writtenOnlyBy` is dropped; the programs changing a store are derived (owner)
The owner asked "Do we need that changedOnlyBy?" and decided: "Yup Drop it". `stored.writtenOnlyBy(…)` and its check
(`WriterNotListed`) are removed. FrFlow derives the programs that change a store from the code: every program calling
an operation that changes the model's state; each is asked to keep the store's rules (`cover_`, `made_`) as before.
"Nothing outside the code changes it" becomes part of what `behavesAs` says: the store does what its model does, and
nothing outside the code changes it. `show` and review of a `behavesAs` assumption state both meanings and list the
programs derived to change the store; when a new program starts changing a store, the claims of `always` about it come
back for review, naming it. Rooms loses `onlyBookingWrites` and has sixteen nodes.

## 32. `atomic`, on the boundary (owner)
The owner: "atomic is good", and, asking "maybe we should make it on boundary?", agreed to the boundary.
`stored.changedOneRunAtATime` becomes `store.atomic` (rooms: `bookingTable.atomic`): runs on the real store never
interleave; each run is one step of the world. `behavesAs` stays on the boundary; `initially` stays on the model,
since it needs the state's type.

## 33. One World (owner)
The owner asked "So a World is a global state. Do we need a global state?" and decided: "Keep one world." A World is
the application at one moment, as the proofs see it: one field per model's state. Code never sees it; in production
the real systems are the state. It lets the roots speak of "the world as it stands" without naming a store, lets
programs and statements span several stores, keeps what an operation does not touch unchanged by construction, and
gives "every reachable world" its meaning. It stays local: a statement mentions only the stores it reads and takes
only their rules as hypotheses, and adding a store brings back for review no statement that does not read it (step 11
tests this). The docs call it the application at one moment, not global state.

## 34. A run is written with `.from` (owner)
The owner chose option A: `program(inputs).from(world) { (answer, after) => … }`, with
`.failing { (error, after) => … }` for what holds when it fails. Today's `.answer(world)` and `.after(world)` are not
carried into the rebuild; the one form covers programs that fail.

## 35. A boundary has a Model; `StateModel` and `AssumedModel` are its kinds (owner)
The owner asked "can we somehow abstract over StateModel and Boundary? Like, we could have any Model for Boundary, one
kind being StateModel" and chose the name: "AssumedModel is okay". Every boundary has one model (`boundary.model(…)`),
tied to it by `behavesAs`. A `StateModel[S]` gives its operations as changes to a state, a field of the World; programs
run on it exactly, and the adapter is tested against it on generated runs. An `AssumedModel` is known only by the
assumptions about its operations (an outside system's promises): Lean sees its operations as unknown, with those
assumptions as hypotheses, and the adapter is tested against them where it can be, trusted otherwise. Owner §30 then
reads "every boundary has a model". No new kind of node, value or quantifier (§15). Built in step 12, where the first
outside systems are ported; rooms is unchanged.
Superseded by §36: there is no boundary and no `AssumedModel`; `StateModel` stays, as the meaning of a Definition's
operations on a state.

## 36. No `Boundary`: what FrFlow cannot see is a Definition (owner)
The owner: "I think we should just get rid of Boundary then. Custom scala code has the same nature as external app."
He asked for it to be done first ("1. Yes": step 11b, before step 12), and chose how one system's operations are
written: "A for now" (each operation its own Definition, not a trait). So:
- There is no `Boundary`. Everything FrFlow cannot see inside is a Definition given plain Scala, whether the project
  wrote it or it calls an outside system.
- An operation on a state (a Definition of type `A => Program[R]`) gets its meaning from a `StateModel[S]`, which says
  what each operation does to its state (`inRoom.means(…)`, `add.means(…)`). The state is a field of the World.
  Programs call the operations as any Definition (`inRoom(request.room)`), and the plain Scala is tested against the
  model on generated sequences of calls.
- A Definition known only by assumptions is the "assumed" case: tested against them where possible, trusted otherwise.
- `behavesAs` goes. Its two meanings become the generated-run test and an assumption on the model,
  `stored.onlyCodeChanges`. `atomic` moves to the model (`storedBookings.atomic`).
- The clock becomes Definitions with their model. The programs changing a state are those calling an operation whose
  meaning changes it (derived, §31). Lean sees what it saw: each operation runs on its field of the World.
- This supersedes the boundary wording of §30 and all of §35. Every Definition must have a meaning, as `check` already
  requires, so `BoundaryUnchecked` and `AssumedModel` go, and so does a boundary's call written in a statement: an
  operation is a Definition, run as `add(b).from(now) { … }`.

## 37. `made_` at the call: proven, never checked at run time (owner)
The owner: "With proof yes, but not at runtime. No runtime checks." Every argument proven code hands to plain Scala (a
function or an operation on a state) meets the `always` rules on its type, on every path:
- It is asked at every call, never left to `cover_`.
- The results of a Definition known only by assumptions are values from outside, covered only by an assumption of
  `always` on their type (§21).
- Calls from proven defines count, as calls from programs do.
It is a Lean obligation only; the rebuild has no run-time checks (§2).

## 38. Fingerprints of code written beside nodes (owner)
The owner: "Ok". In a file that holds nodes, only the definitions the code refers to are fingerprinted (each to the next
line at its indentation or less, with the same file's definitions those name), so code written beside nodes is
governed, and editing a node beside it brings nothing back. Other files are governed whole, as before.

## 39. Hand-written consistency proofs (owner)
The owner: "Yes, handwritten is okay, agent can write proofs.." A consistency group FrFlow cannot witness (promises that
are not equations, such as keycloak's `sessionLookup` and crm's `recordsByQuery`) is proven by a hand-written
`consistent_<i>`; today's `storedSession` and `storedMatching` are the witnesses. An agent may write the proof, Lean
checks it, and the developer decides the nodes as usual.

## 40. The ports' decisions (owner)
The owner: "Ok" and "ok".
- crm's tables hold one row per key: a claim of `always[CrmStore]`, the rule its generator already drew by.
- `noCrossTenantRead` stays a root.
- `acmeNeverSeesGlobex` becomes an example test (§22).
- auth's `tokensIssuedOnce` ("the session table issues each token to one user") is accepted.
- keycloak's claim on `introspect` is renamed `introspectAnswers`.

## 41. The World is implicit in statements; a run's world after is `.after` (owner)
The owner asked whether the World could be used "without making it a param", then: "Change to world is okay, after
is okay, answer is weird". A statement holds in every reachable world; a value that changes with the world is read in
the current one without being passed a world (no marker: see §43);
a program in a statement runs from the current world, and `.after` is the world it leaves (`storedBookings.in(
book(request).after)`). What the program returns is `.result` (owner: "I accept recommended"; `.answer` refused); for a program that can fail it is `Either[Error, A]`. This replaces the run form of §34. Built as step 13b.

## 42. One `Flow`; `Program` removed (owner)
The owner: "Oh I hate Program. We should make it one Flow". A Definition that may read or change state has the type
`A => Flow[R]`, and its code is written as a plain `Flow[R]` (a `for` comprehension), as today's library writes it; the
tagless form (`[F[_]]`, `using f: Flow[F]`, `f.flatMap`) stays inside the library. Built as step 13b.

## 43. No marker for values that change; `.isConstant` (owner)
The owner asked "Why do we need marker for varying though?" and decided: "Let's do as you say but make a .isConstatnt
assumption". Every Declaration may change with the World (Lean sees a function of the world); a fixed one is the case
where it is the same in every world. A `define` changes with the World exactly when its body reads state (a model's
state or a program's `.result`/`.after`), which FrFlow reads off the code. Programs are known by their type
(`A => Flow[R]`). `d.isConstant` says a Declaration is the same in every world; it is written as an assumption
(`Node.assumption("The opening hour never changes.")(openingHour.isConstant)`) and, like any formula, may also be
claimed where the code shows it. Built as step 13b.

## 44. `isConstant` on any value: no next step changes it (owner)
The owner: "We may want to keep various values constant. How now, with World, would you say that a value stays
constant?", then, of `closed(room) implies bookingsOf(room).isConstant`: "It is not constant overall but stays for
some kind of continuous moment", and "Keep isConstant". `t.isConstant` applies to any value, not only a Declaration.
In a statement (which holds in every reachable world) it means that no run of any program from the current world
changes `t`: `∀ w ∈ Reach, cond(w) → t(after(p, w)) = t(w)` for every program `p` (TLA+ `□[cond ⇒ t′ = t]`); the
condition is read in the world before the step. Over a stretch of steps where the condition holds, `t` stays the same;
with no condition it is the same in every reachable world (∃c ∀w ∈ Reach, t(w) = c). It is proven by one obligation
per program that changes what `t` reads; a new such program brings the statement back for review. Of a Declaration,
which no code gives a value, it is an assumption.

