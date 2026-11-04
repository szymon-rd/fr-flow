package frflow.api.node.lean

import frflow.core.expr.Value

/** Why a check ended where it did: Lean ran out of time; the model or the shared lemmas do not build; a proof file
  * holds what is not allowed (each with its line); an obligation is not proven; a try Lean proved shows nothing the
  * node says can hold; a proof rests on axioms beyond those allowed; or a step is refuted on a case (its inputs).
  */
enum FindingView:
  case LeanTimedOut
  case ModelDoesNotBuild(errors: List[Message])
  case ProofNotAllowed(what: List[(Int, Forbidden)])
  case LemmasDoNotBuild(errors: List[Message])
  case NotProven(errors: List[Message])
  case Refuted(tries: List[TryView])
  case DisallowedAxioms(axioms: List[String])
  case StepRefuted(inputs: List[(String, Value)])
