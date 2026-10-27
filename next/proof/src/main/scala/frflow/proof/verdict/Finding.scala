package frflow.proof.verdict

import frflow.proof.obligation.TryKind
import frflow.proof.reading.{Diagnostic, NotAllowed}

/** Why a check ended where it did, as data (the CLI and the web view say it). */
enum Finding:
  case LeanTimedOut
  case ModelDoesNotBuild(errors: List[Diagnostic])
  case ProofNotAllowed(what: List[(Int, NotAllowed)])
  case LemmasDoNotBuild(errors: List[Diagnostic])
  case NotProven(errors: List[Diagnostic])
  /** A try Lean proved that shows nothing the node says can hold (`clash`, `unsat`). */
  case Refuted(tries: List[TryKind])
  /** Axioms a proof rests on beyond `ProofRules.AllowedAxioms`. */
  case DisallowedAxioms(axioms: List[String])
