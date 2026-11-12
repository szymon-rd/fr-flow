package frflow.project.rocq

import frflow.project.Projects
import frflow.proof.rocq.RocqProject
import java.nio.file.{Files, Path}
import scala.annotation.experimental

/** The payments model printed as Rocq and checked by `coqc`: every definition and statement is read by Rocq, and
  * FrFlow's tactic proves the obligations it can. Run by `sbt rocqTest` (it needs `coqc`).
  */
@experimental class PaymentsRocqSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(60, "min")

  test("the payments model is read by Rocq, and its tactic proves obligations".tag(Rocq)) {
    val project = RocqProject(Projects.bare(Projects.elaborated(payments.payments)).modules)
    val dir = sys.env.get("FRFLOW_ROCQ_DIR").fold(Files.createTempDirectory("frflow-rocq"))(Path.of(_))
    val checked = RocqRun.check(project, dir)
    val impls = checked.compiled.filter(_.endsWith("/Impl.v"))
    val shown = impls.filter(f => checked.open(f).isEmpty)
    println(s"Rocq: ${checked.compiled.size} files read, ${checked.broken.size} broken, " +
      s"${project.unprinted.size} not printed; impl proven by frflow_auto: ${shown.size} of ${impls.size}")
    impls.foreach(f => println(s"  ${if checked.open(f).isEmpty then "proven" else "open  "} $f"))
    assertEquals(project.unprinted, Map.empty[String, String])
    assertEquals(checked.broken, Map.empty[String, String])
    assert(shown.sizeIs >= 19, s"frflow_auto proves ${shown.size} of the code obligations, where it proved 19")
  }
