package frflow.project.effects

import frflow.core.effect.{ClassName, Program}
import frflow.dsl.compiled.effect.EmitEffects
import frflow.project.Live
import frflow.project.rocq.ThreadsRocq
import frflow.proof.effect.PrintProgram
import java.nio.file.{Files, Path}

/** Compiled Scala read as trees of effects, tested against the JVM: the sample classes (`samples`) are read from
  * their TASTy, each scenario is run on the JVM, and Rocq runs the scenario's tree (`FrFlow/Effect/Run.v`): the
  * two must give the same number. `FRFLOW_ROCQ_WRITE=1` writes the kept file anew.
  */
class EffectRunSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  private val kept = Path.of("modules/project/src/test/resources/effects/Samples.v")
  private lazy val program: Program = EmitEffects(classOf[samples.Scenarios], _.contains("/effects/samples/"))
  private lazy val text: String = PrintProgram(program)

  /** Each scenario, by its name, with what it gives on the JVM. */
  private def onTheJvm: List[(String, Int)] =
    classOf[samples.Scenarios].getDeclaredMethods.toList.filter(m => m.getParameterCount == 0).sortBy(_.getName)
      .map(m => m.getName -> m.invoke(samples.Scenarios()).asInstanceOf[Int])

  test("the trees read from the sample classes are the ones kept") {
    if sys.env.contains("FRFLOW_ROCQ_WRITE") then
      Files.createDirectories(kept.getParent)
      Files.writeString(kept, text): Unit
    assertEquals(text, Files.readString(kept))
  }

  test("every class, field and method of the samples has its name, and nothing outside them is called") {
    assertEquals(program.classes.map(_.value).sorted,
      List("Account", "Bank", "Counter", "Numbers", "Pair", "Scenarios"))
    assertEquals(program.outside, Nil)
    assertEquals(program.methods.count(_.name.name == "new"), program.classes.size)
  }

  test("Rocq runs each scenario's tree, and it gives what the JVM gave".tag(Live)) {
    val runs = EffectRuns.file("Effects.Samples", ClassName("Scenarios"), onTheJvm)
    val library = List("Effect/Tree", "Effect/Int32", "Effect/Sig", "Effect/Run")
    assertEquals(onTheJvm.map(_._1), List("banking", "computing", "counters", "draining", "sharing", "wrapping"))
    assertEquals(ThreadsRocq.failing(List("Effects/Samples.v" -> text, "Effects/Runs.v" -> runs), library), None)
  }
