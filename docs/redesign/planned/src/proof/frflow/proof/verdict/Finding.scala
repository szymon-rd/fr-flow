package frflow.proof.verdict

import frflow.proof.reading.{Diagnostic, NotAllowed}

/** Why a check ended where it did, as data (the CLI and the web view say it). */
enum Finding:
  case LeanTimedOut
  case ModelDoesNotBuild(errors: List[Diagnostic])
  case WaitsForChoice(terms: List[String])
  case ProofNotAllowed(what: List[(Int, NotAllowed)])
  case LemmasDoNotBuild(errors: List[Diagnostic])
  case LeanAndScalaDisagree(example: Int)
  case NotProven(errors: List[Diagnostic])
