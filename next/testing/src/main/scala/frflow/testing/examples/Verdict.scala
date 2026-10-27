package frflow.testing.examples

import frflow.dsl.build.ElabError
import frflow.eval.run.OnCode

/** What `sbt test` says of one example: what the code says of it (`ExampleRun`); that it has no Scala value, so is
  * checked against the claims in Lean only (`NoValue`, or about Declarations); that its code threw (its message: a
  * fault of the code or its wiring, a value it reads not given); or that it, or the knowledge base it is about,
  * could not be read.
  */
enum Verdict:
  case Ran(onCode: OnCode)
  case LeanOnly(onCode: OnCode)
  case Threw(message: String)
  case NotRead(errors: List[ElabError])
