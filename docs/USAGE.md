# Using FrFlow

The reference for the CLI and what it checks. The [README](../README.md)
explains the idea; [DAG.md](DAG.md) is the design.

## Running

Requirements: JDK 17+, sbt, and Lean 4.35.0 (`lake` on the `PATH`, or
`FRFLOW_LAKE`). `bin/frflow PROJECT COMMAND` runs a project's CLI
(`bin/frflow auth tree`), compiling with sbt on first use and after a change.
`--help` lists the commands. `sbt test` runs the tests.

## Commands

| | command | what it does |
|---|---|---|
| developer | `tree [NODE]` | the DAG from the root (or below NODE): status, kind and state, statement |
| | `show NODE`, `diff NODE` | a node in about a screen; what changed since it was decided |
| | `inbox` | what waits for whom, then the summary |
| | `review` | decide what waits, parents first: `[a]ccept [r]eject [s]kip [v]iew [q]uit [?]ask` |
| | `accept NODE...`, `reject NODE`, `confirm`, `revisit NODE`, `gone NODE` | one decision, with `-m REASON`; confirmed on a terminal, `--yes` without one |
| | `ask NODE TEXT`, `ask --idea TEXT`, `close REQUEST...` | ask the agent for a change; close an answer read |
| | `serve [--port N] [--as NAME]` | the same in a browser: the [web view](#web-view) |
| agent | `inbox`, `context NODE`, `find WORDS\|PATH` | what to do; everything on a node (`show --full`); where a change belongs |
| | `render`, `check [NODE]`, `scaffold NODE` | Lean and `.frflow/kb.json`; prove what changed; proof stubs for what is left open |
| | `status`, `ci` | the tree, the summary and the warnings; exit 1 unless complete (`ci` checks first) |
| | `answer REQUEST\|NODE TEXT` | reply to a request, or tell the developer of work they did not ask for |

`--as NAME` names who decides (default: `FRFLOW_AS`, or the name the key is
filed under). `serve` and the commands that decide ask for it when neither is
set.

## Output and exit codes

On a terminal the output has colors and Unicode and fits the terminal's width:
formulas, diffs and decisions wrap, other lines are cut (`context` shows them
whole). `--plain`, `NO_COLOR` or `TERM=dumb` turn this off. Off a terminal (CI,
agents, a pipe) the output is plain ASCII and no line is cut. `--json` on
`tree`, `show`, `inbox`, `status` and `check` prints the typed value.

Exit codes: 0 fine; 1 not complete, or a decision refused; 2 a usage error
(an unknown node too); 3 no Lean.

## Nodes

| Kind | Written as | In Lean |
|---|---|---|
| claim | `Node.claim(id, statement, why)(formula)`; the one with no parents is the root | proven from its parts (`complete`) |
| invariant | `Node.invariant[A, B](id, statement, why)(rule)`, kept by contracts with `.keeps(inv)(view)` | a claim whose parts are its keepers |
| contract | `Node.contract(op)(id, statement, why)(post)` on an operation `op: Param[(A, B) => R]` | every call of `op` meets `post`; an attached `define` is proven against it (`impl`) |
| assumption | `Node.assumption(op)(...)(post)`, or `Node.assumption(id, statement, why)(formula)` | trusted, not proven: what the outside does, or a fact of the world |
| definition | `Node.definition(id, statement, why)(Type := of[T], term := expr, ...)` | fixes terms of the vocabulary; decided, not proven |
| design | `Node.design(id, statement, why)(files*)` | none: governs code no proof covers |

`.under(parents*)` makes a node a part of each parent. `.replaces(other)` marks
an alternative: accepting one rejects the other. Two definitions of one term
are alternatives too. The root speaks in open terms (`Opaque` types, `Param`
terms); definitions bring in the domain as it is needed.

## Decisions

The developer decides every node, once. The agent proposes, with a `why` and
examples; no command of the agent's decides. `.frflow/ledger.json` holds each
decision: who, the reason, the alternatives rejected, the commit, a signature,
and the decision before it.

- **A parent decides its parts.** Adding or removing a part puts the parent up
  for review.
- **Order.** A proposal waits until its parents and the definitions it uses
  are accepted.
- **Mechanical decisions.** A node under review whose own content did not
  change, that Lean proves again (not a definition or design node): one batch,
  `confirm`.
- **Signing.** The developer's key is kept outside the repository
  (`~/.config/frflow/signing.key`, or `FRFLOW_KEY`) and created on the first
  decision; its public key is filed as `.frflow/keys/NAME.pub` and committed.
- **Refused.** A decision on a node that moved since the developer looked at
  it, or with a reason of only a word or two.

A decision binds the reason to the hash of what the developer saw. Whatever
moves under it puts the node back up for review, with the cause:

| Cause | What moved | Shown as |
|---|---|---|
| `self` | what the node says: statement, formula, `why`, examples, terms, kept invariants, implementation source, its section of the idea | a line diff per field |
| `above` | the meaning of a parent, of a definition it uses, or of a contract its code calls | the diff of what moved |
| `parts` | its list of parts | the parts added and removed |
| `code` | the files it governs | a git diff since the decision's commit |
| `revisit` | the developer said a change above may affect it | their reason |
| `merged` | two branches decided it, and the merge kept both | both decisions |

Rewording a `why` or a statement whose formula is unchanged does not cascade
below; a change of formula does. Accepting a change lists every decision that
rests on it, and the developer marks those it may affect (`--revisit`).

## What Lean proves

For each node N with parts C1..Cn, over the open terms they mention, with the
definitions in force applied:

| Obligation | Statement | Fails when |
|---|---|---|
| `complete` | C1 → … → Cn → N | not proven: the parts do not make N (open) |
| `needed_C` (n ≥ 2), tried | N without C | Lean proves it: C is not needed |
| `vacuous` (n = 1), tried | N, with no hypothesis | Lean proves it: N says nothing its part adds |
| `restates` (n = 1), tried | N → C1 | Lean proves it: N says what its part says (a warning) |
| `clash`, tried | C1 → … → Cn → False | Lean proves it: the parts contradict each other |
| `unsat` (every claim), tried | ¬ N | Lean proves it: no world meets N |
| `idle` (the root), tried | the root, with every operation doing nothing | Lean proves it: the root does not say what users can do |

`complete` is proven by `frflow_auto` or by hand. The tries use automation
with a small budget, so they catch only what it can show. Then:

- **Composition.** Each node gets `holds`: the leaves below it imply it.
  `root_impl` states the root of the code (each operation with a proven
  `define` replaced by it) from the assumptions alone.
- **Implementations** written as a `define` meet their contract (`impl`),
  proven from the promises of the operations they call, not from their code.
- **Invariants.** A rule over pairs (a reader, a record shown to them). Every
  contract in its scope keeps it (`.keeps`) or says why it is exempt
  (`.exempt`).
- **Examples, both ways.** Lean evaluates each example whose parameters are
  values (or `bindTable` lookups), and probes near them: it must prove what
  Scala computes and not its opposite.
- **State.** A run is `es.foldLeft(init)(step)`; the library (`FrFlow.always`,
  `simulates`, `tracks`) proves properties of every run.
- **Authored proofs** (`lean/Proofs/<KB>/<Node>.lean`) state exactly the
  generated obligation and have their axioms audited (`sorry` fails).

**Checked by running.** Examples run against the contract and the
implementation. In production, `service` binds the operations to their code
and checks every result against the contract (or `checkedBy`, a cheaper check
proven to follow from it), raising `ContractViolation`.

**Effects are assumptions.** A database or a clock is an assumption on an
operation; the code is proven from its promise. The adapter (SQL) is checked
against a proven `define` on the examples, on varied data and on every call.
In `examples/crm`, a seeded SQL bug (a dropped `WHERE`) is stopped this way
while every proof still holds.

## What is trusted, and the limits

Lean proves the nodes consistent with each other and the root of the code;
the developer decides that they are the right theory. Trusted:

- the assumptions (the hypotheses of `root_impl`), checked where they can be;
- the Scala-to-Lean translation, cross-checked on the examples and on probes
  near them; it refuses what it cannot translate faithfully (`Int`
  arithmetic);
- that parameters hold the data they are said to mean, and that every path to
  the data goes through `service`: design nodes are reviewed, not proven;
- the signing key, kept outside the repository the agent edits;
- the model's program. FrFlow runs it to read it, so the gate stops drift, not
  an agent that writes code to subvert FrFlow.

Limits: the tries are one-sided. Examples with function-valued parameters
(other than `bindTable`) are not evaluated in Lean. Running covers the
examples and their combinations, not every input. Ordering, liveness, and
effects outside a pure core behind `service` are not covered. Maps and sets
cannot be iterated.

## Warnings

`status` exits 1 unless every node is accepted, nothing is left unproven, no
node is gone, and there is no warning. The warnings:

- no developer key, or a decision not signed by a filed key;
- a source file governed by two nodes or by none, or a governed file that
  does not exist;
- a section of `IDEA.md` no node names, or one a node names that the idea
  lacks;
- a proof file of no node;
- a contract none of whose examples Lean evaluates;
- a node that only restates its part.

## CI

Committed: the Scala, `IDEA.md`, `.frflow/` (ledger, keys, requests) and
`lean/Proofs`; the rest is derived. CI runs `ci`, caching
`.frflow/checks.json` and `lean/.lake` by branch, so only what changed is
proven again.

## A new project

A project is a directory beside the examples (here `examples/library`):

1. `IDEA.md`: a title, a lead paragraph, `## ` sections, and `## Not modelled`.
2. `lazy val library = example("library")` in `build.sbt` (and the project in
   `root`'s `aggregate`), then `sbt reload`.
3. The model in `src/main/scala/library/`, ending with the knowledge base and
   its command line:
   ```scala
   val knowledge = KnowledgeBase("Library", idea = "IDEA.md")(lendsExactly, ...)
   object libraryCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/library", serve = Some(frflow.web.WebView.serve))
   ```
   With several mains, set `Compile / run / mainClass`.
4. `bin/frflow library render` creates `lean/` (its `lakefile.toml`,
   toolchain and the generated Lean); then `check` and `status`.

## Web view

`bin/frflow PROJECT serve [--port N] [--as NAME]` serves the developer's flow
in a browser: the DAG with each node's state and status, a node with its diff
since it was decided, the inbox, the decisions with their reasons, and
requests to the agent. It listens on localhost (port 8765 by default) and
prints a link with a random token, which every route asks for.

The page is a client of the same API as the CLI (`FrFlowApi`), so a decision is
signed and recorded as `accept` records it, and the CLI can run beside it. The
server runs the model it compiled when it started: once the model's sources
change, the page says so and refuses decisions until it is restarted. Agents
use the CLI, not the web view.

## Modules

One sbt subproject each, under `modules/`:

- `protocol`: the data crossing modules and files, with JSON codecs.
- `model` (package `frflow`): nodes and knowledge bases; `Opaque`, `Param`,
  `define`; the macro; examples, probes, `service`.
- `lean`: the Lean of a knowledge base, and reading Lean's output.
- `ledger`: review states and decision rules; reports; stores, keys and
  signatures.
- `check`: render and check (running `lake`), the snapshot, status, scaffold,
  git.
- `api`: `FrFlowApi`, the typed operations a front end calls.
- `cli`: the command line over the API.
- `web`: the web view over the API. The CLI does not depend on it.

The Lean library is in `lean/FrFlow/`. The MCP server is on the branch
`web-view`, which will become a separate repository.

## Measurements

`python3 bench/generate.py N` writes `examples/scale`, a synthetic project:
one root over N services grouped five by five, each service a claim with two
or three parts and a contract with proven code. `bench/measure.sh 20 60`
times a cold check, then one change of each kind. On a 4-core container:

| nodes | cold `check` | one code change | one claim change | one definition change | `status` |
|---|---|---|---|---|---|
| 103 | 92 s | 14 s | 15 s | 45 s | 2.2 s |
| 305 | 234 s | 19 s | 21 s | 125 s | 4.3 s |

The code change is one service's code; the claim change strengthens one
service's part; the definition change is a limit about a third of the nodes
use. After a cold check, only what a change reaches is proven again.
