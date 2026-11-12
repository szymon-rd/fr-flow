package frflow.dsl.build

import frflow.core.name.RelPath

/** What is wrong with a part of a model, wherever it is found: in a term being built, a constant, a path, a link. */
enum Fault:
  case DeclaredLater
  case NoType(where: String)
  case FunctionEquality
  case NotData(value: String)
  /** A field the record's type does not have (a selector the derivation did not make). */
  case NoField(name: String)
  /** A value only plain code reads, its Scala type with no `LeanType`, spoken of in a statement (its field selected):
    * the type can derive one if a statement should speak of it.
    */
  case CodeOnlyInStatement(scalaType: String)
  case BadPath(path: String, why: RelPath.Invalid)
  /** `.leftOpenAbove` on a node that is not a claim. */
  case NotAClaim(what: String)
  /** `define` given a Definition that carries no proven code. */
  case NotProvenCode(definition: String)
  /** A meaning given to a Definition that has its own where it is written (`define`). */
  case MeantWhereWritten(definition: String)
  /** An `always` that is not a node's whole formula (under a `forall`, `!`, `implies`, `||`, in a define): only a
    * node's formula is a rule, every value it ranges over meeting what always holds; anywhere else it would range
    * over every value the prover has, made or not.
    */
  case AlwaysInside
  /** `contractOf[T]` of a type whose `FrSpec` states no contract (`FrSpec.derived[T].where(v => …)` states one). */
  case NoContract(scalaType: String)
  case Thrown(message: String)
  /** A statement reads a structure as it stands beside two structures that hold it: which one's is not said
    * (`ledger.total.in(handler.current)` says it).
    */
  case HeldByTwo(structure: String, holders: List[String])
  /** Two classes of examples of one model of one name (`setName`): their examples' theorems would be one. */
  case ExampleSetsClash(name: String, classes: List[String])
