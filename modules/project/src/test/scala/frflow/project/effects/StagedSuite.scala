package frflow.project.effects

import frflow.core.code.Datum
import frflow.core.staged.{Stage, StagedCode}
import frflow.dsl.compiled.source.ReadSource
import frflow.project.Live
import frflow.project.rocq.ThreadsRocq
import frflow.proof.rocq.StagedModule
import java.nio.file.{Files, Path}

/** Code staged from its trees into programs (`frflow.core.staged.Stage`): the sample classes, whose programs are
  * kept and checked by Rocq, and Ox, of which what is staged is counted. That a staged program does what the code
  * does on the JVM is tested where the programs are run (`frflow.project.rocq.OxRunSuite`).
  * `FRFLOW_ROCQ_WRITE=1` writes the kept file anew.
  */
class StagedSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  private val kept = Path.of("modules/project/src/test/resources/effects/Samples.staged.v")
  private def trees(of: List[(String, Datum)]): List[Datum] = of.sortBy(_._1).map(_._2)
  private lazy val samples_ : StagedCode =
    Stage(trees(ReadSource.only(classOf[samples.Scenarios], _.contains("/effects/samples/"))))
  private lazy val text: String = StagedModule(samples_)

  private lazy val ox_ : List[(String, Datum)] = ReadSource(classOf[ox.Ox])
  private val read = Set("ox/internal/ThreadHerd.tasty", "ox/OxError.tasty", "ox/unsupervised$package.tasty",
    "ox/supervised$package.tasty", "ox/fork$package.tasty")

  test("the programs staged from the sample classes are the ones kept, and nothing of the samples is left out") {
    if sys.env.contains("FRFLOW_ROCQ_WRITE") then Files.writeString(kept, text): Unit
    assertEquals(text, Files.readString(kept))
    assertEquals(samples_.unstaged, Nil)
  }

  test("of the five files of Ox the Ox model reads, every method, initialiser, function and argument by name is " +
    "staged: 107 programs") {
    val staged = Stage(trees(ox_.filter((path, _) => read.exists(path.endsWith))))
    assertEquals((staged.units.size, staged.unstaged), (107, Nil))
  }

  test("of the whole of Ox, all is staged but three methods that make a lazy value") {
    val staged = Stage(trees(ox_))
    assertEquals(staged.unstaged.map(_._2).distinct, List("a lazy value made in a method"))
    assertEquals(staged.unstaged.map(_._1).sorted, List("ox.flow.FlowOps.groupedWeightedWithin",
      "ox.flow.FlowTextOps.decodeStringUtf8", "ox.flow.internal.groupByImpl$package$.groupByImpl"))
    assertEquals(staged.units.size, 3054)
  }

  test("Rocq checks the programs staged from the sample classes".tag(Live)) {
    val library = List("Base", "Executions", "Jvm/Prog", "Jvm/Machine", "Scala/Tree", "Scala/Program", "Scala/Table",
      "Scala/Equal", "Scala/Value", "Scala/Meaning", "Scala/Jdk", "Scala/Library", "Code/Outside", "Code/Staged")
    assertEquals(ThreadsRocq.failing(List("Effects/Staged.v" -> text), library), None)
  }
