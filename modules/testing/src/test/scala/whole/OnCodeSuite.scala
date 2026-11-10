package whole

import frflow.*
import frflow.eval.term.Semantics
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

  test("an example reading a provided value it does not give: no Scala value, it is checked in Lean only") {
    val open = new FrFlowExamples(auth.Auth.model):
      example("no session is open"):
        auth.Sessions.sessions is auth.Sessions(Nil)
    assertEquals(onCode(open).map(_._2),
      List(OnCode.NotEvaluated(frflow.eval.EvalError.Unbound(auth.Sessions.sessions.name))))
  }

  test("an example the code does not meet fails on it") {
    val wrong = new FrFlowExamples(auth.Auth.model):
      example("Alice gets into /b", auth.Grant.grants := Nil, auth.Sessions.sessions := auth.Sessions(Nil)):
        auth.Admission.admit("t1", auth.Path("/b")) is Some(auth.UserId("alice"))
    assertEquals(onCode(wrong).map(_._2), List(OnCode.Fails))
  }

  test("knowledge.code: a Definition's plain code over the values given, as production calls it") {
    val admit = auth.Auth.model.code(auth.Admission.admit)(
      auth.Grant.grants := List(auth.Grant(auth.UserId("alice"), auth.Path("/a"))),
      auth.Sessions.sessions := auth.Sessions(List(auth.Session("t1", auth.UserId("alice")))))
    val decided = (admit("t1", auth.Path("/a")), admit("t1", auth.Path("/b")))
    assertEquals(decided, (Some(auth.UserId("alice")), None))
  }

  test("knowledge.code: a value given wins, and a Definition with no meaning given none is refused") {
    val grants = List(auth.Grant(auth.UserId("bob"), auth.Path("/c")))
    assertEquals(auth.Auth.model.code(auth.Grant.grants)(auth.Grant.grants := grants), grants)
    intercept[IllegalArgumentException](auth.Auth.model.code(auth.Grant.grants)())
  }

  test("d.fn: a define called from plain code, over the values it is given") {
    val env = frflow.core.code.Values(Map(auth.Grant.grants.name -> (() => List(auth.Grant(auth.UserId("ann"),
      auth.Path("/d"))))))
    val grantFor = auth.Grant.grantFor.fn(env)
    val decided = (grantFor(auth.UserId("ann"), auth.Path("/d")), grantFor(auth.UserId("ann"), auth.Path("/e")))
    assertEquals(decided, (true, false))
  }
