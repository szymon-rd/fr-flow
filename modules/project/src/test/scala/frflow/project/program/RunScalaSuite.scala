package frflow.project.program

import cats.effect.IO
import frflow.core.expr.Value
import frflow.core.name.{ModelName, NodeId}
import frflow.eval.Races
import frflow.eval.run.OnCode
import frflow.project.Projects
import frflow.project.port.RunCode
import frflow.project.check.{CheckProgram, Refutations}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{CheckStatus, Finding, ProverRun}
import frflow.project.port.memory.ScriptedLake

/** Running Scala before the pure phases: an example whose code throws is said so; the witnesses Lean is given hold
  * no races' winners; and a step its one part fixes the answer of is refuted on a case, which Lean proving it
  * makes a finding of the step's check.
  */
class RunScalaSuite extends munit.CatsEffectSuite:
  private val steps = Projects.elaborated(Steps.steps)

  test("an example whose code throws is said to have thrown, with the code's message") {
    val e = Projects.elaborated(Steps.broken)
    val examples = Steps.BrokenExamples().elaborated.fold(es => fail(es.toString), identity)
    Projects.inMemory(Map.empty).flatMap(p => Projects.analysed(p, e, examples)).map(a =>
      assertEquals(a.computed.examples.map(_._2), List(OnCode.Threw("the service is down"))))
  }

  test("a world Lean is given holds no races' winners, however deep it is") {
    val world = Value.World(List(ModelName("stored") -> Value.Many(Nil), Races.model -> Value.Many(Nil)), Nil)
    assertEquals(Races.without(Value.Tuple(List(Value.Maybe(Some(world))))), Value.Tuple(List(Value.Maybe(Some(
      Value.World(List(ModelName("stored") -> Value.Many(Nil)), Nil))))))
  }

  test("a step its one part fixes the answer of only above zero is refuted below it") {
    Refutations(RunCode.inline[IO]).of(Projects.bare(steps), NodeId("nonNegative")).map(found =>
      assert(found.exists(_.inputs.forall {
        case (_, Value.Num(n)) => n < 0
        case _                 => false
      }), found))
  }

  test("when complete does not go through and Lean proves the case refutes the step, the check says so: it fails") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, steps, Nil)
      lake <- ScriptedLake[IO](Scripted(a, Set("complete"), Set.empty).answer, installed = true)
      out  <- CheckProgram(p.files, lake, "lean", RunCode.inline[IO])(a, Some(NodeId("nonNegative")))
    yield
      val c = out._1.headOption.getOrElse(fail("not checked"))
      assertEquals(c.status, CheckStatus.Failed)
      assert(c.results.exists(r => r.name == ObligationName.Complete), c.results)
      assert(c.findings.exists { case Finding.StepRefuted(List(("n", Value.Num(n)))) => n < 0; case _ => false },
        c.findings)
  }

  test("refuted on a case Lean does not prove, the step's check says nothing more") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, steps, Nil)
      lake <- ScriptedLake[IO](m => if m.dotted.endsWith("Refutes") then
                ProverRun.Failed("error: FrFlowGen/Steps/nonNegative/Refutes.lean:1:0: unknown constant")
                else Scripted(a, Set("complete"), Set.empty).answer(m), installed = true)
      out  <- CheckProgram(p.files, lake, "lean", RunCode.inline[IO])(a, Some(NodeId("nonNegative")))
    yield assertEquals(out._1.flatMap(_.findings), Nil)
  }
