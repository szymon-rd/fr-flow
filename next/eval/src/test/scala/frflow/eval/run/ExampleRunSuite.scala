package frflow.eval.run

import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.eval.Semantics

/** An example checked against the code (owner §18): its fact evaluated with `echo` given its Scala. */
class ExampleRunSuite extends munit.FunSuite:
  private def onCode(code: String => String): OnCode =
    val theory = Echo.theory(code)
    ExampleRun(Semantics(Elaborated(theory, Map.empty, Nil)), theory).of(Example("echoes hi", Nil, Echo.example))

  test("an example the code meets holds of the code; one it does not, fails") {
    assertEquals(onCode(identity), OnCode.Holds)
    assertEquals(onCode(_ => "wrong"), OnCode.Fails)
  }
