package frflow.project.pipeline

import frflow.core.example.Gen
import frflow.core.name.NodeId
import frflow.decision.content.Sha

/** What a node's test report depends on: the node as decided (its content: its formula, how its code is written),
  * the code it governs as the lexer reads it, how the tests run (cases and seed), the generators given and what each
  * is said to make, and the examples (their cases are counted first). A change to any of them tests it again.
  */
object TestKeys:
  /** How tests are made and run: a change to it tests every node again. */
  val Version: Int = 1

  def of(a: Analysis, id: NodeId): String =
    val e = a.valid.elaborated
    Sha.parts((List(Version.toString, Contents.of(a.canonical, id).ref,
      a.governed.get(id).fold("")(_.fingerprint.sha), a.inputs.settings.cases.toString,
      a.inputs.settings.seed.value.toString) ++
      e.generators.map(g => s"${g.ty}: ${said(g.gen)}") ++
      a.computed.examples.map((x, _) => s"${x.name}: ${x.fact.source.value}"))*)

  private def said(g: Gen[?]): String = g match
    case Gen.Described(_, says) => says
    case _                      => ""
