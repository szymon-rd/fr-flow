package frflow.eval.flow

import cats.effect.unsafe.implicits.global
import frflow.core.expr.{Prog, Progs}

/** Recording agrees with running: a program's recorded `Prog`, run by `FlowInterpreter` on the models, gives what the
  * program itself gives run in production (`Running`) on the models' instances, its result or its error, and the
  * models' states after; for every combinator, failing runs and a failing boundary's calls among them. Each run is
  * also what the program should give.
  */
class FlowAgreementSuite extends munit.FunSuite:
  (Steps.all ++ AtOnce.all).foreach { p =>
    test(p.name) {
      val (models, running) = (Runs.onModels(p).unsafeRunSync(), Runs.running(p).unsafeRunSync())
      assertEquals(models, p.expected, "on the models")
      assertEquals(running, models, "running, against the models")
    }
  }

  test("every kind of step is run: loops, errors, failing calls, concurrent steps, transactions") {
    val steps = (Steps.all ++ AtOnce.all).flatMap(p => Progs.all(Runs.recorded(p)))
    val kinds = steps.map(_.getClass.getSimpleName).toSet
    List("Loop", "Collect", "Accumulate", "Branch", "Raise", "Catch", "Call", "Par", "ParEach", "Race", "Guard",
      "Atomic").foreach(k => assert(kinds(k), k))
    assert(steps.exists { case Prog.ParEach(_, _, _, limit) => limit.contains(2); case _ => false })
  }
