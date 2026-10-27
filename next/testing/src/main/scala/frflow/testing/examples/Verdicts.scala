package frflow.testing.examples

import frflow.dsl.example.FrFlowExamples
import frflow.eval.Semantics
import frflow.core.Theory
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.testing.NoValue

/** Each example of a class, in the order written, checked against the code of the knowledge base it is about. */
object Verdicts:
  def of(written: FrFlowExamples): List[(String, Verdict)] = written.knowledge.elaborated.fold(
    es => written.examples.map(_.name -> Verdict.NotRead(es.iterator.toList)),
    e =>
      val run = ExampleRun(Semantics(e), e.theory)
      written.examples.map(x => x.name -> x.elaborated.run.fold(es => Verdict.NotRead(es.iterator.toList),
        (_, elaborated) => verdict(e.theory, run.of(elaborated)))))

  private def verdict(t: Theory, onCode: OnCode): Verdict = onCode match
    case OnCode.NotEvaluated(e) if NoValue.of(t, e) => Verdict.LeanOnly(onCode)
    case OnCode.Abstract(_)                         => Verdict.LeanOnly(onCode)
    case other                                      => Verdict.Ran(other)
