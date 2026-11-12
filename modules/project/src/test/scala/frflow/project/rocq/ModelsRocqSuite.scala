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

  /** The axioms a proof may rest on: the classical `if` of a model's Booleans, and equal propositions and
    * functions taken as equal.
    */
  private val allowed = Set("classic", "constructive_definite_description", "propositional_extensionality",
    "functional_extensionality_dep")

  /** The lemmas left open, by file, but those of a node's checks: tries that are not to be proven. */
  private def open(checked: RocqRun.Checked): Map[String, List[String]] =
    checked.open.filterNot((file, lemmas) => file.endsWith("/Checks.v") || lemmas.isEmpty)

  test("the payments model is proven in Rocq: the code meets every claim, and the roots follow".tag(Rocq)) {
    val (checked, shown) = read(payments.payments, "payments")
    assertEquals(open(checked), Map.empty[String, List[String]])
    assertEquals(shown.size, 29)
    assertEquals(checked.assumed.diff(allowed), Set.empty[String])
    assert(RocqRun.lemmas(checked, "FrFlowGen/Payments/RootImpl.v").contains("RootImpl_root_impl"))
  }

  test("the auth model is proven in Rocq: each node from its parts by its proof file, the whole consistent".tag(Rocq)) {
    val (checked, _) = read(auth.knowledge, "auth")
    assertEquals(open(checked), Map.empty[String, List[String]])
    assertEquals(checked.stated.keySet.count(_.endsWith("/Theorems.v")), 4)
    assertEquals(checked.assumed.diff(allowed), Set.empty[String])
  }

  test("the rooms model is proven in Rocq: the code books as it checks, and the purpose follows".tag(Rocq)) {
    val (checked, shown) = read(rooms.rooms, "rooms")
    assertEquals(open(checked), Map.empty[String, List[String]])
    assertEquals(shown.size, 5)
    assertEquals(checked.assumed.diff(allowed), Set.empty[String])
  }
