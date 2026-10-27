package whole

import frflow.*
import frflow.eval.Semantics
import frflow.eval.run.{ExampleRun, OnCode}

/** The examples' code as production and the examples run it, from the FrModel alone: every example of the
  * five checked against the code (`ExampleRun`), a Definition's code as plain code calls it (`knowledge.code`), and a
  * define called from plain code (`d.fn`).
  */
class OnCodeSuite extends munit.FunSuite:
  private def onCode(written: FrFlowExamples): List[(String, OnCode)] =
    val e = Theories.elaborated(written.knowledge)
    val run = ExampleRun(Semantics(e), e.theory)
    written.elaborated.fold(es => fail(es.iterator.mkString), identity).map(x => x.name -> run.of(x))

  test("every example of the five that gives the values it reads holds of the code it is about") {
    List(rooms.GrantedExamples(), auth.DecisionExamples()).foreach { written =>
      onCode(written).foreach((name, verdict) => assertEquals(verdict, OnCode.Holds, name))
    }
  }

  test("crm's example reads the history it does not give: no Scala value, it is checked in Lean only") {
    assertEquals(onCode(crm.ExpectationsExamples()).map(_._2),
      List(OnCode.NotEvaluated(frflow.eval.EvalError.Unbound(crm.history.name))))
  }

  test("an example the code does not meet fails on it") {
    val wrong = new FrFlowExamples(auth.knowledge):
      example("Alice gets into /b", auth.grants := Nil, auth.sessions := auth.Sessions(Nil)):
        auth.admit("t1", auth.Path("/b")) is Some(auth.UserId("alice"))
    assertEquals(onCode(wrong).map(_._2), List(OnCode.Fails))
  }

  test("knowledge.code: a Definition's plain code over the values given, as production calls it") {
    val admit = auth.knowledge.code(auth.admit)(auth.grants := List(auth.Grant(auth.UserId("alice"), auth.Path("/a"))),
      auth.sessions := auth.Sessions(List(auth.Session("t1", auth.UserId("alice")))))
    val decided = (admit("t1", auth.Path("/a")), admit("t1", auth.Path("/b")))
    assertEquals(decided, (Some(auth.UserId("alice")), None))
  }

  test("knowledge.code: a value given wins, and a Definition with no meaning given none is refused") {
    val grants = List(auth.Grant(auth.UserId("bob"), auth.Path("/c")))
    assertEquals(auth.knowledge.code(auth.grants)(auth.grants := grants), grants)
    intercept[IllegalArgumentException](auth.knowledge.code(auth.grants)())
  }

  test("d.fn: a define called from plain code, over the values it is given") {
    val env = frflow.core.code.Values(Map(auth.grants.name -> (() => List(auth.Grant(auth.UserId("ann"),
      auth.Path("/d"))))))
    val grantFor = auth.grantFor.fn(env)
    val decided = (grantFor(auth.UserId("ann"), auth.Path("/d")), grantFor(auth.UserId("ann"), auth.Path("/e")))
    assertEquals(decided, (true, false))
  }
