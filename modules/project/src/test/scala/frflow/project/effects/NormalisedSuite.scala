package frflow.project.effects

import frflow.core.effect.{ClassName, MethodName}
import frflow.core.normal.{Interpret, NormalProgram, Show}
import frflow.dsl.compiled.normal.Normalise
import java.nio.file.{Files, Path}

/** Stage 1 of the translation, on the sample classes: the normalised Scala read from their TASTy is the one
  * kept, and run by its interpreter each scenario gives what the JVM gives. `FRFLOW_ROCQ_WRITE=1` writes the
  * kept file anew.
  */
class NormalisedSuite extends munit.FunSuite:
  private val kept = Path.of("modules/project/src/test/resources/effects/Samples.normal")
  private lazy val program: NormalProgram = Normalise(classOf[samples.Scenarios], _.contains("/effects/samples/"))

  /** Each scenario, by its name, with what it gives on the JVM. */
  private def onTheJvm: List[(String, Int)] =
    classOf[samples.Scenarios].getDeclaredMethods.toList.filter(m => m.getParameterCount == 0).sortBy(_.getName)
      .map(m => m.getName -> m.invoke(samples.Scenarios()).asInstanceOf[Int])

  test("the normalised Scala read from the sample classes is the one kept") {
    if sys.env.contains("FRFLOW_ROCQ_WRITE") then Files.writeString(kept, Show(program)): Unit
    assertEquals(Show(program), Files.readString(kept))
  }

  test("run by the interpreter, each scenario gives what the JVM gives") {
    val scenarios = ClassName("Scenarios")
    val gave = onTheJvm.map((name, _) => name -> Interpret.scenario(program, MethodName(scenarios, name)))
    assertEquals(gave, onTheJvm.map((name, n) => name -> Interpret.Value.Whole(n)))
    assertEquals(gave.size, 9)
  }

  test("a method the program does not have does not run") {
    intercept[Interpret.Stuck](Interpret.scenario(program, MethodName(ClassName("Scenarios"), "missing")))
  }
