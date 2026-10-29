package frflow.project.pipeline

import frflow.core.example.Gen
import frflow.core.analysis.outside.Guards
import frflow.core.name.{ModelName, NodeId}
import frflow.decision.content.Sha
import frflow.project.code.CodeFingerprints
import frflow.testing.model.ModelRuns

/** What a node's test report depends on: the node as decided (its content: its formula, how its code is written),
  * the code it governs as the lexer reads it, how the tests run (cases and seed), the generators given and what each
  * is said to make, and the examples (their cases are counted first). A change to any of them tests it again.
  */
object TestKeys:
  /** How tests are made and run: a change to it tests every node again. */
  val Version: Int = 1

  def of(a: Analysis, id: NodeId): String =
    a.decided.theory.code.implemented.keys.find(ModelRuns.reportedUnder(_) == id).fold(node(a, id))(model(a, _))

  private def node(a: Analysis, id: NodeId): String =
    keyed(a, List(Contents.of(a.canonical, id).ref, a.governed.get(id).fold("")(_.fingerprint.sha)))

  /** A model's runs: the model as Lean is given it, its operations' Scala as written and its files, and what always
    * holds of its state, which the runs' states are drawn meeting.
    */
  private def model(a: Analysis, m: ModelName): String =
    val t = a.decided.theory
    val scala = t.code.implemented.get(m)
    keyed(a, CodeTexts.lean(a.decided, m).toList.flatten ++ scala.map(_.written.value) ++
      scala.map(i => CodeFingerprints.of(i.files.map(f => f -> a.inputs.sources.get(f))).fingerprint.sha) ++
      Guards.reading(t, List(m)).map(_._1).distinct.map(n => Contents.of(a.canonical, n).ref))

  private def keyed(a: Analysis, parts: List[String]): String =
    Sha.parts((List(Version.toString) ++ parts ++ List(a.inputs.settings.cases.toString,
      a.inputs.settings.seed.value.toString) ++
      a.valid.elaborated.generators.map(g => s"${g.ty}: ${said(g.gen)}") ++
      a.computed.examples.map((x, _) => s"${x.name}: ${x.fact.source.value}"))*)

  private def said(g: Gen[?]): String = g match
    case Gen.Described(_, says) => says
    case _                      => ""
