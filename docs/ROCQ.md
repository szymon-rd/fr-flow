# Rocq: the prover FrFlow is moving to

FrFlow is moving from Lean to Rocq. This page says what is built, how to run it, and what is left. Until the
move is finished, Lean remains what checks a project (`frflow check`, `sbt leanTest`); Rocq is run by its own
tests (`sbt rocqTest`).

## What is built

- **The printer** (`modules/proof/src/main/scala/frflow/proof/rocq/`). `RocqProject(modules)` takes the modules
  FrFlow generates for a model (`Analysis.modules`: types, definitions, each node's statements and theorems) and
  gives each as a `.v` file. It prints the same tree the Lean printer prints, so a model has one lowering.
- **The library** (`modules/proof/rocq/FrFlow/Base.v`): what the generated definitions are written with (`ite`,
  `List_filter`, `List_foldl`, …) and the tactics the generated theorems call (`frflow_auto`,
  `frflow_witness`). It uses Rocq's standard library alone.
- **The run** (`modules/project/src/test/scala/frflow/project/rocq/RocqRun.scala`, for the tests): `coqc` on each
  file after those it imports. `coqc` stops at a file's first error, so a lemma whose proof fails is admitted and
  the file compiled again; the lemmas not proven are those admitted.

## How a model reads in Rocq

| The model | Lean | Rocq |
|---|---|---|
| `Boolean` | `Prop`, under `open Classical` | `Prop`; `if` is `ite`, decided by `excluded_middle_informative` |
| `BigInt`, `String` | `Int`, `String` | `Z`, `string` |
| a case class | `structure Decision` | `Record Decision := Decision_mk { Decision_card : string; … }` |
| a field read, `d.card` | `d.card` | `card_of d` (a class `Has_card`, an instance for each record with the field) |
| a field replaced | `{ l with decisions := ds }` | `with_decisions l ds` |
| an enum's case | `Account.OfCard` | `Account_OfCard` |
| a constant in a namespace | `Payments.commitMovesPast.Obl.impl` | `commitMovesPast_Obl_impl` |
| a list's fold, filter | `List.foldl`, `List.filter` | `List_foldl`, `List_filter` (the library's, Lean's argument order) |
| a quantifier over members | `∀ d ∈ ds, p` | `forall d, In d ds -> p` |
| a pair's parts | `p.1`, `p.2` | `fst p`, `snd p` |

Rocq has one scope of field names and no namespaces that can be reopened, which is why a field is read through
a class and a constant is named by its whole path. Axioms used: `classic` and
`constructive_definite_description` (the classical `if`), and, where two propositions or two functions are
proven equal, `propositional_extensionality` and `functional_extensionality`.

## Where it stands

`ModelsRocqSuite` prints two examples and checks them with Rocq 9.3:

- `examples/payments`: Rocq reads all 122 generated files, and `frflow_auto` proves 22 of the 29 code
  obligations (`impl`). Lean's `frflow_auto` proves 26 of them; it rests on `simp` and `grind`, which Rocq's
  standard library has no match for, so the Rocq tactic is a set of rewrites, case splits, `lia` and
  first-order search, extended obligation by obligation.
- `examples/auth`: Rocq reads every generated file. The four statements that a node follows from its parts
  (`complete`) are not proven by the tactic; Lean proves them by hand too (`lean/Proofs/Auth`).

A lemma the run reports proven may rest on one it admitted (a node's `holds` on its `complete`): the run in
the product reads `Print Assumptions` to tell.

## Rocq on a machine

The newest Rocq is installed through opam (`opam install rocq-prover`), on the system's OCaml; the tests call
`rocq compile`, or what `FRFLOW_ROCQ` names.

## What is left, in order

1. **The tactic**: the seven payments obligations still open, then the examples' theorems (`Whole`).
2. **The run in the product**: a `Prover` port beside `Lake`, `_CoqProject`, reading `coqc`'s output per
   theorem, the rules a hand proof file must keep (no `Axiom`, `Admitted`, `Parameter`), and the audit
   (`Print Assumptions`).
3. **Hand proofs**: `rocq/Proofs/<Model>/<node>.v`, written by hand: payments (5 Lean proof files) and auth (5).
   The other examples (90 Lean proof files) stay on Lean until they are moved.
4. **Programs** (`Flow`: rooms, keycloak, crm): the printer does not print a `do` block, a class or an instance
   yet (`RocqProject.unprinted` names each such module). They are lowered to state-passing terms, and the
   library's `Flow`, `Faults`, `Races`, `Clock`, `Commute` and `Machine` are written in Rocq.
5. **Lean removed**: the Lean printer, library, proofs and `Lake`.

A node's signed content is today its printed Lean. It stays printed by that printer through the move, so no
decision in a ledger is reopened by it; what the content is printed as afterwards is a decision for then.
