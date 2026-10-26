# r43 review, round 6 (design revision 6)

## Verdict: APPROVED

0 blocking and 0 major findings are open. Two minors remain: R6.1 (new) and R3.14 (accepted).

---

## For the owner: what to know before approving

**What you are approving.** A rebuild of FrFlow in place, as a compiler, in 20 steps, each one reviewable change.

**The design.**
- **One typed IR.** It is made once by elaboration:
  - `Expr` for terms and `Prog` for flows;
  - `Statement`, one case per node kind;
  - `Edge`, `CodeTable` and `Vocabulary`.
- **Typed phases.** Elaborate, validate, resolve, then obligations, then the Lean AST, then text. Each phase is a pure
  function, and the Lean, Scala, run-time and test back ends are interpreters of the same IR.
- **Decisions on their own.** They are a pure module over a narrow `Subject` per node.
- **Effects behind algebras, where they pay.** Files, Lean, git, the ledger and the keys are algebras over `F[_]`
  because each has a second interpreter or a law suite. Concrete `IO` appears only in `main`, the server and the
  terminal. The core takes no effect type.
- **Thirteen modules.** Each has one top package, and a build test checks their edges.

**What has been verified.** The planned code is 384 files and about 7,500 lines including tests, with the bodies that
carry the design written. It compiles with `-Werror`, and its 33 tests pass. Among them:
- **Lean.** Four of crm's generated Lean files are reproduced byte for byte from the Lean AST, with a post, a flow and
  two obligations lowered from the IR.
- **Proof files.** Each of today's authored-proof rules has a test.
- **Decisions.** A design moved under another node comes back for review, a short reason is refused, and a gone
  node's decision is signed.
- **Running services.** A broken contract is reported and then thrown. An outside system's adapter, called from
  proven code, is checked on each call (crm's seeded SQL-bug case in miniature).
- **Examples.** An example's wrong result from the code is reported.

Every claim I checked against today's code and the four examples' ledgers holds: the Lean output, field order and
texts of contents, signatures, review states, the invariant scope and the mechanical rule.

**What you decide (§4.8).**
- **A. Encoding of terms and flows.** The recommendation is an initial encoding (data and folds), keeping today's DSL
  syntax.
- **B. Ambient state.** Two named ambient scopes (fresh variables while elaborating, values in force while plain code
  runs), plus one memo per define.
- **C. Boundaries.** Today's trait of operations, its signatures derived by a macro. Tagless boundaries would be a
  later proposal.
- **D. How far in one step.** Strangler steps pinned by goldens, not a new repository.
- **E. Module granularity.** Thirteen modules, not six.
- **F. Code fingerprint.** Scala without comments, with lines and indentation kept.
- **G. Existing decisions.** A one-time signed `confirm --rebind` moves them to the new content form and fingerprint.
  You run it with your key on the four examples at step 12.
- **Drop candidates.** Unused flow combinators: `race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM`.

Your earlier change is applied throughout: no `IDEA.md`, no idea sections, no numbered questions. Old ledgers still
read and verify.

**What changes for users, by design.**
- A comment-only or reformatting edit of a governed file no longer brings a node back, once the ledger is rebound.
- `.frflow/kb.json` and `--json` change shape (steps 15–16). FrFlow never reads them back; tools that do must follow.
- The examples' test sources are rewritten at step 17.
- The examples' sources lose `idea = …`, and each gets a README from its `IDEA.md` (step 12).
- No decision moves except through `--rebind`, which you sign.

**Size.** The result is about the same size as today (about 11,650 lines against 12,008), in more and smaller files
(about 520 against 347). It is not smaller. The gain is that every concept has one place and one shape.

### Placeholders that remain (62 `???` in 43 files), and why they are acceptable
- **Ports whose shape a written neighbour fixes.**
  - The remaining operator cases in `LowerPrim`, `LowerProg`, `LowerValue`, `DenotePrim`, `Denote`, `Literals` and
    `Reflect` (written cases sit beside them).
  - `Required.feasible`, `impl`, `check`, `covers` and `expects`, which are written like `complete` and the tries.
  - `Validate.code`, whose cases exist in `Problem`.
  - `Reading.waitsFor`, `Below.movedOnlyWith` and `Meaning.decisionMoved`, ports of today's rules whose neighbours are
    written and tested.
- **Text renderings that must equal today's byte for byte** (`Texts`: examples, keeps, uses, implementation, model,
  run check). Step 0's golden pins each node's content.
- **Lean module layout** (`NodeModules`, `VocabularyModules`, `RootImplModule`). The AST and the lowering are shown
  able to say their content. Step 5 adds a reproduced module of every kind before they replace today's printer.
- **Interpreters and macros whose interface and laws are fixed:**
  - `Lake.make`, `LedgerStore.file`/`inMemory`, `ProjectFiles.make`;
  - `DataMacros`, `BoundaryMacros`, `Captures`, `Spans`, the `Lexer`;
  - `PropertyTests`, the flow examples on the models, `CheckPlan`, `NodeChecker`'s steps;
  - the API's live interpreter.

None of these hides a design decision. Each is either pinned by a golden or written to an interface the planned code
already uses.

### Main risks (from §6, with my view)
- **Lowering differs from today's printer.**
  - *What could happen:* a case the examples do not show prints differently, moving check hashes.
  - *Mitigation:* the fixtures' goldens and the translation kept until both agree.
  - *My view:* this is the riskiest technical step (step 5).
- **Temporary growth.**
  - *What could happen:* about 2,500 more lines at the peak (step 8), while old and new representations coexist.
  - *Mitigation:* one representation is removed per step.
- **Macros versus reflection.**
  - *What could happen:* `Data`, `BoundaryOps`, `Source.of` and `Source.valName` replace today's reflection, and may
    behave differently on types or lambdas the examples lack.
  - *Mitigation:* errors are elaboration errors naming the site.
- **Rewriting tests.**
  - *What could happen:* about 5,200 lines of FrFlow's tests are rewritten over the steps.
  - *Mitigation:* each suite keeps its case names, and each step lists the cases it drops.
- **Other users' ledgers before `--rebind`.**
  - *What could happen:* until they run it, an edit to `.leftOpenAbove` or a failure clause is not noticed.
  - *Mitigation:* `status` warns while old-form decisions remain (`Warning.OldForm`).
- **Downgrade.** An older FrFlow reading a rebound ledger shows every node as moved. The release note covers it.

### What the first three steps will show
- **Step 0, pin behaviour.** A golden suite over the four examples:
  - every generated Lean file and proof stub;
  - each node's content reference and hash, code fingerprint and review state;
  - every signature verified;
  - the snapshot and CLI outputs;
  - a ledger round trip.

  Plus the architecture test with today's module edges as its allowed list. Nothing in FrFlow changes. From then on,
  any change to a pinned output fails a test.
- **Step 1, delete the drop candidates you approve** (`race`, `guarantee`/`bracket`, `timeout`, `parTupled`, `ifM`).
  The goldens are unchanged: no example uses them.
- **Step 2, one top package per module.** `private[frflow]` becomes each module's own package. The about 40 places
  where one module uses another's internals become explicit, listed as debt in the architecture test. The examples'
  tests compile through a compatibility facade. No behaviour changes.

  This is the first step where the module boundaries are real and visible.

The IR itself first appears at step 3, the IR-based analyses at step 4 (the regexes over printed Lean are deleted),
and the Lean back end at step 5.

---

## Status of round-5 findings

| Finding | Status | Checked in |
|---|---|---|
| R5.1 (major) adapters of assumptions not wired | **resolved** | `Running.operations` takes every `Contract` or `AssumedCall` with code (the first listed per operation); `Wiring.needed` adds what the code calls (`Tested.calls`, or the proven define's mentions) and the examples' givens; `ServiceSuite`: an adapter with a seeded SQL bug, called from a contract's proven code, is reported and thrown; an operation with neither code nor binding is `Unbound` when wired |
| R5.2 mutable state undercounted | resolved | `AssumptionWatch` and `Sampling` docs name the watch's cell and the samplers' counters |
| R5.3 examples' givens at wiring | resolved | `Statement.givens`; `Wiring.needed` |
| R5.4 data for a code-only symbol | resolved | `Problem.DataForCodeOnly` in `Validate.givens`; `Givens` takes `typeOf: SymbolName => Option[Ty]` and treats data for an untyped symbol as a FrFlow bug, which `Validate` rules out |

**On R5.4's placement.** `Validate` is the right place, rather than an elaboration `Fault`. Whether a symbol is
code-only is a fact of its declaration, which may come from another node's terms. Only once the vocabulary is
assembled from every declaration can a node's givens be compared with it. That is a cross-reference rule, like the
other `Problem`s, and it is reported with all of them at once.

## Remaining minors
- **R6.1 (new).** `Wiring.needed` is stricter than today's `needed`: it also requires the symbols a proven define
  mentions to be bound. A service whose proven code mentions a symbol neither bound nor defined, and that today wired
  and failed only on the call reaching it, now fails at wiring. That is the better behaviour, but it is a change. The examples' tests at step 14 will show whether any example relied on the lazier rule. List it in the step's
  behaviour notes.
- **R3.14 (accepted).** The result is about today's size, in about 50% more files.
