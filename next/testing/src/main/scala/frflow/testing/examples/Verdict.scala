package frflow.testing.examples

import frflow.dsl.build.ElabError
import frflow.eval.run.OnCode

/** What `sbt test` says of one example: what the code says of it (`ExampleRun`), or that it, or the knowledge base it
  * is about, could not be read.
  */
enum Verdict:
  case Ran(onCode: OnCode)
  case NotRead(errors: List[ElabError])
