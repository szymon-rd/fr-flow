package frflow.testing.examples

import frflow.dsl.example.FrFlowExamples
import frflow.eval.Semantics
import frflow.eval.run.ExampleRun

/** Each example of a class, in the order written, checked against the code of the knowledge base it is about. */
object Verdicts:
  def of(written: FrFlowExamples): List[(String, Verdict)] = written.knowledge.elaborated.fold(
    es => written.examples.map(_.name -> Verdict.NotRead(es.iterator.toList)),
    e =>
      val run = ExampleRun(Semantics(e), e.theory)
      written.examples.map(x => x.name -> x.elaborated.run.fold(es => Verdict.NotRead(es.iterator.toList),
        (_, elaborated) => Verdict.Ran(run.of(elaborated)))))
