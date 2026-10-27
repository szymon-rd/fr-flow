package frflow.testing.ported

import frflow.KnowledgeBase
import frflow.core.code.Code
import frflow.core.name.NodeId
import frflow.dsl.example.FrFlowExamples
import frflow.eval.Semantics
import frflow.eval.run.OnCode
import frflow.testing.{Plan, PropertyTests, Settings}
import frflow.testing.derive.Derive
import frflow.testing.examples.{Verdict, Verdicts}
import frflow.testing.report.{Count, Failure, Outcome, TestReport}

/** An example's generated tests as `check` runs them: the reference's settings (1,000 cases from `FRFLOW_SEED=1`),
  * drawn by the derived generators seeded by its examples.
  */
object Tested:
  def report(kb: KnowledgeBase, node: String, examples: List[FrFlowExamples] = Nil,
      settings: Settings = Settings.default): Option[TestReport] =
    val e = kb.elaborated.fold(es => throw AssertionError(es.iterator.mkString("\n")), identity)
    val written = examples.flatMap(_.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity))
    PropertyTests(Semantics(e), e.theory).of(NodeId(node), Plan(settings, Nil), Derive.of(e, written))

  /** A node's code passing every case it was asked for (the reference's 1,000, all drawn), each part reached. */
  def passes(kb: KnowledgeBase, node: String, examples: List[FrFlowExamples] = Nil): TestReport =
    val r = report(kb, node, examples).getOrElse(throw AssertionError(s"$node is not tested"))
    if r.outcome != Outcome.Passed || r.count != Count(1000, 1000) || r.unreached.nonEmpty then
      throw AssertionError(s"$node: ${r.outcome}, ${r.count}, unreached ${r.unreached}")
    r

  /** The nodes whose code is plain Scala, tested: each claim or assumption about a Definition with tested code. */
  def nodes(kb: KnowledgeBase): List[String] =
    val e = kb.elaborated.fold(es => throw AssertionError(es.iterator.mkString("\n")), identity)
    val tested = e.theory.code.attached.collect { case (d, a) if a.code match { case Code.Tested(_, _) => true
      case _ => false } => d }.toSet
    e.theory.nodes.map(_.node).filter(_.statement.definition.exists(tested)).map(_.id.value)

  def failure(kb: KnowledgeBase, node: String): Failure.Call =
    report(kb, node).flatMap(_.failure).collect { case f: Failure.Call => f }
      .getOrElse(throw AssertionError(s"no case of $node fails"))

  /** Each example of a class, what the code says of it. */
  def onCode(written: FrFlowExamples): List[OnCode] = Verdicts.of(written).map(_._2).collect {
    case Verdict.Ran(v) => v
  }
