> Kept as written. Its paths are those of the design workspace: `r43-design/` is `planned/`, `r43-spike/` is
> `lean-spike/` (its `rooms-lean-r15/` build), `r43tools/` is `tools/`, all under `docs/redesign/`; its section numbers
> are those of `history/ARCHITECTURE-r15-log.md`.

# r43 review, round 15 (revision 15)

**Verdict: APPROVED.** 0 blocking, 0 major, 5 minor.

- **Build:** `sbt clean compile proof/test decision/test dsl/test project/test evaluation/test testing/test` passes, with
  21 + 7 + 11 + 88 + 18 + 2 = **147 tests**, exit 0 (`r43-review15-sbt.log`).
- **Lean:** `r43-spike/rooms-lean-r15/` builds with `lake` (19 jobs). It proves 18 theorems with no `sorry`, using only
  the axioms `propext`, `choice` and `Quot.sound`.
- **§15 core concepts:** held strictly. There are three node kinds, one `Definition` type, `Declaration` kept out of
  code, two quantifiers, and one premise edge.

## For the owner, before approving

**What you are approving.** A ground-up rebuild of FrFlow in 12 modules, built beside today's under `next/` and
replacing it example by example (§6, steps 0–15). Every one of your decisions is applied in the planned code, not
only in prose:
- **Three kinds of nodes:** `Node.claim`, `Node.assumption`, `Node.design`. How a claim is checked is derived from
  its formula and from what gives each Definition its meaning; `show` prints it.
- **Two kinds of values:** `Declaration` (statements only, enforced at compile time) and `Definition` (`define` and
  `program` return one). A Definition gets its meaning from one of: `implementProven`, `implementTested`,
  `implementValue`, `implementProvided`.
- **Two quantifiers:** `forall` and `always`. `always[T]` is a hypothesis in Lean, met where values are made
  (`made_<maker>`). `always(store)` is kept by every program writing the store (`cover_<op>`), from its start.
- **The world outside** is five kinds of assumption, each written as a node and linked by `.assuming`. FrFlow checks
  that each claim lists what it rests on.
- **Consistency and vacuity:**
  - consistency is proven by group, with witnesses derived from equations, bounds and proven code; "consistency not
    proven" is its own status;
  - vacuity is guarded by `inhabited_` and `satisfiable_`;
  - examples are ordinary tests that nothing depends on.
- **Terms are tagless-final.** There is one printer (Lean) and one evaluator (Scala) of terms, and no run-time
  checking.

**Remaining placeholders, and why they are acceptable.** There are 40 `???` in 31 files, each assigned to a §6 step,
and each one's parts are already written and tested. The ones you will meet first:

| Placeholder | Step | Why it is acceptable |
|---|---|---|
| `BoundaryOps` derivation (`derives BoundaryOps`) | 2 | Rooms' `BookingsOps` writes by hand everything the macro must produce except `lifted`, which 4.3 describes. |
| derived generators and shrinking | 5 | `PropertyTests.of` runs 500 cases; `CalendarSuite`'s hand-written draw shows what the derived one must do (R15.3). |
| `made_<maker>` for a program's result | 3 | `made_inRoom` (a model's result) is written and proven; rooms' programs return no constrained type. |
| the examples' munit runner | 5 | Examples are checked by `ExampleRun` and in Lean (`example_<i>`); only the runner is missing. |

**Main risks** (the full table is at the end of §6):
- **Lean proofs are still written per node.** `Proofs.lean` proves rooms' `impl` and `cover_book` by hand, as today's
  examples are proven. FrFlow derives the obligations and their witnesses, not the proofs.
- **A claim with no Scala value cannot be tested.** One that quantifies over every moment, like rooms' `grantWhenFree`,
  is proven from its parts but not tested against code. `show` and `status` say so. The same limit forced the
  `always[RoomBookings]` rule to be stated in start and end times (R15.4).
- **Size and compile time.** The plan is about 10,000 lines, near today's 12,000. Compiling rooms is about 1.3× slower.
- **The README.** The readers' latest findings are partly addressed (table below). Their double reading of `always` is
  your decision to keep or split.

**What the first three steps show you:**
- **Step 0** records today's outputs as the reference: every Lean module, each node's standing, `status`/`show`/`review`
  text, and the seeded bugs. Nothing in FrFlow changes.
- **Step 1, `next/core`:**
  - the term algebras and their interpreters, and the three-kind statements with `Range` and `CallForms`;
  - validation: roots, parts of proven code, meanings, and premises;
  - consistency groups and witnesses;
  - property and law suites, with today's validation cases kept by name.
- **Step 2, `next/dsl`:**
  - the user's forms: `Node.claim`/`assumption`/`design`, `Declaration`/`Definition`, `forall`/`always`, the outside
    formulas, `.refines`/`.assuming`, `FrFlowExamples`, `implement…`;
  - the macros;
  - the tagless programs and boundaries;
  - every node of the five examples written in the three kinds, before any example is ported. This is the first place
    you can read your examples in the new forms.

## Round-14 findings, checked in the code

| Id | Status | Evidence |
|---|---|---|
| R14.2 *Definition* as two types (blocking) | **Fixed** | `define`/`program` return `Definition[A => R]` / `Definition[A => Program[R]]` (`Defines.scala:18-26`, through `Definition.onTheSpot`). `Def`, `Def1`, `Def2` and `Steps` are deleted. The core's body is `core.term.Body`. |
| R14.3 premises derived, not written | **Fixed** | `.assuming` is the only premise mechanism. Rooms writes each claim's premises (`Rooms.scala:48-68`), and `Premises.of` checks them (`BookSuite`: "each check rests on the outside facts its `.assuming` lists"; a missing one is refused). |
| R14.1 calendar over reachable states | **Fixed** | `RoomBookings derives LeanType`; `roomBookingsApart = always[RoomBookings](r => r.bookings.pairwise(noOverlap)).assuming(storeModel, neverOverlap)`. The model's `inRoom` makes one. `made_inRoom` is written and proven (`AlwaysSuite`; the Lean spike). The README's binary-search `Calendar` is restored. `CalendarSuite`: 500 generated cases meeting the rule pass, with more than 50 sharing a room; on a list the store cannot give the calendar is wrong, and no case draws one. |
| R14.4 names | **Fixed, pending today's renames** | `FrFlowExamples`, `initially`, `changedOneRunAtATime`, `.assuming` written. See R15.1. |
| R14.5 whole-formula claims | **Fixed** | Tested on their drawn variables. A claim with no Scala value shows "not checked", and `Warning.NotChecked` is raised (`CheckingSuite`). |
| R14.6 witnesses by substitution order | **Fixed** | `AuthSuite`: "a group solved in substitution order: access is witnessed once signedIn and authorized are". |
| R14.7 `provided` | **Fixed** | `implementProvided`. |
| R14.8 size | **Accepted** | 40 `???`, each given a step. |

**Is `vocab.Define` a second name for Definition? No.** It is the vocabulary's record of what a `define { … }` was
elaborated to (its name, written lambda and form). It is internal and named after the owner's own keyword. The user
sees one concept, `Definition`. A Definition implemented by another (`book` by `bookIfGranted`) is two Definitions,
as the owner describes it, not two names for one.

## The README readers' v7 findings against the rebuild's forms

| Finding (today's rooms) | Rebuild | Avoided? |
|---|---|---|
| `World` never introduced (`before: Term[World]`) | unchanged | **No:** a README line, or the name (R15.2) |
| vague assumption names (`startsMeetingItsRules`, `calledWithInputsMeetingTheirRules`) | `stored.initially(held => held === Nil)` names its predicate; `outside.calls(book)` still does not say which rules | **Half** (R15.2) |
| `.checkedAgainst(start, observe)` unclear | the same form | **No** (R15.2) |
| report wording (`complete open`, `(changed, above)`) | `Texts` and `Checking` lines are plain sentences ("proven of book's program, bookIfGranted", "rests on …"). Status lines are ported in steps 9–10. | **Mostly**: keep the wording rule for the port |
| node names in code vs reports | ids are the vals' names as written | **Yes** |
| why `always[RoomBookings]` holds | `.assuming(storeModel, neverOverlap)` on it, with `made_inRoom` proven | **Yes** |
| `always` with two (three) meanings | the owner's two quantifiers | **The owner's decision**, passed on |
| `Calendar.byRoom` groups a single room's bookings | still grouped (`Calendar.scala:121`) | **No:** minor (R15.2) |
| 12 nodes listed by hand in `KnowledgeBase` | the same | **No:** minor (R15.2) |

## Minor findings

- **R15.1 — names pending today's renames.**
  - Today's library now says `bookingTable`/`storedBookings`, and is renaming `startsMeetingItsRules`. Rooms here says
    `store`/`stored` and `startsEmpty` (today: `startsApart`).
  - Settle them once today's renames land, in step 11's port of rooms, so the README and the rebuild share one name
    each.
- **R15.2 — the readers' remaining items, for the rebuild's forms.**
  - `outside.calls(book)` should name what it guarantees, or `show` should spell out the rules it covers. One option
    is `book.calledOnlyWith(endsAfterStart)`, naming the `always` claims, but that changes the outside formula and is
    the owner's call.
  - Give `checkedAgainst` parameters that say their roles (`startFrom`, `readBack`), with one line of doc.
  - Introduce `World` where it is first used, in the README and in `Worlds`' doc.
  - `Calendar` should filter by the request's room rather than group. `RoomBookings` may hold several rooms, so it
    must still filter; it need not group. Alternatively add "of one room" to the rule.
  - `Validate` warns when a node val reached by an edge is missing from the `KnowledgeBase` list (or the list is
    collected).
- **R15.3 — drawn values must meet the rules of their fields.**
  - Lean assumes `always[Booking]` of every booking inside a `RoomBookings` (`Guarded`). `Respecting` applies only the
    top-level rule. `CalendarSuite` makes its bookings end after they start in a hand-written `Draw`.
  - The derived generators of step 5 must respect every `always[T]` of every value of `T` inside a drawn value (fields,
    list elements), as `Guarded` does in Lean. Otherwise tests judge code on cases the claims exclude.
  - Add one test that a drawn `RoomBookings` meets `endsAfterStart` for each booking.
- **R15.4 — rules without a Scala value.**
  - `roomBookingsApart` had to be stated in `noOverlap`, because a rule over all moments cannot be drawn against. The
    name says "apart" while the rule is `noOverlap`; rename it, or say so in its statement.
  - Make the limit a validation message: "this `always[T]` has no Scala value: values of `T` cannot be drawn meeting
    it; state it in evaluable words and prove the link". Do not leave it only as a risk-table row.
- **R15.5 — `outside.calls` and `endsAfterStart`'s five premises.**
  - `endsAfterStart.assuming(fromTheForm, storeModel, oneAtATime, startsEmpty, onlyBookingWrites)` is long.
  - The store's four facts recur on every claim about the store. Consider letting an assumption group them (one node
    "the store is run as modelled") if the owner agrees. It stays one edge, one kind.

## Most important open findings

None are blocking or major. In order of value:
1. **R15.3:** drawn values must meet their fields' rules in step 5.
2. **R15.2:** the readers' remaining items (`outside.calls`, `checkedAgainst`'s parameters, `World`, `byRoom`, the
   node list).
3. **R15.1:** settle names with today's library at the rooms port.
