package frflow.project.rocq

import frflow.dsl.kb.FrModel
import frflow.project.Projects
import frflow.proof.rocq.RocqProject
import java.nio.file.{Files, Path}
import scala.annotation.experimental

/** The examples' models printed as Rocq and checked: every definition and statement is read by Rocq, and
  * FrFlow's tactic proves the obligations it can. Run by `sbt rocqTest` (it needs Rocq).
  */
@experimental class ModelsRocqSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(60, "min")

  /** The model's Rocq, checked with the example's proof files (`examples/<example>/rocq/Proofs`): every file
    * read; and the files of code obligations (`impl`) proven, by the tactic or by a proof file.
    */
  private def read(model: FrModel, example: String): (RocqRun.Checked, List[String]) =
    val elaborated = Projects.elaborated(model)
    val proofs = RocqProofs.of(Projects.base.resolve(s"examples/$example/rocq"))
    val project = RocqProject(Projects.proving(elaborated, RocqProofs.stated(proofs)).modules)
    val kept = sys.env.get("FRFLOW_ROCQ_DIR").map(d => Path.of(d, elaborated.theory.name.value))
    val checked = RocqRun.check(project, kept.getOrElse(Files.createTempDirectory("frflow-rocq")), proofs)
    val lemmas = checked.open.toList.sortBy(_._1).filter((file, _) => RocqRun.lemmas(checked, file).nonEmpty)
    lemmas.foreach((file, open) => println(s"  $file: ${RocqRun.lemmas(checked, file).map(l =>
      (if open.contains(l) then "open " else "proven ") + l).mkString(", ")}"))
    assertEquals(project.unprinted, Map.empty[String, String])
    assertEquals(checked.broken, Map.empty[String, String])
    (checked, checked.compiled.filter(f => f.endsWith("/Impl.v") && checked.open(f).isEmpty))

  test("the payments model is read by Rocq, and its tactic proves obligations".tag(Rocq)) {
    val (_, shown) = read(payments.payments, "payments")
    assert(shown.sizeIs >= 26, s"frflow_auto proves ${shown.size} of the code obligations, where it proved 26")
  }

  test("the auth model is proven in Rocq: each node from its parts by its proof file, the whole consistent".tag(Rocq)) {
    val (checked, _) = read(auth.knowledge, "auth")
    val open = checked.open.filterNot((file, lemmas) => file.endsWith("/Checks.v") || lemmas.isEmpty)
    assertEquals(open, Map.empty[String, List[String]])
    assertEquals(checked.stated.keySet.count(_.endsWith("/Theorems.v")), 4)
  }
