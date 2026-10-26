package frflow.eval.run

import cats.effect.kernel.Sync
import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.example.{CallExample, RunEnd, RunExample}
import frflow.core.expr.{Binder, Expr, Prog, Value}
import frflow.core.name.NodeId
import frflow.core.spec.{Promise, Statement}
import frflow.core.ty.Ty
import frflow.eval.{Denote, Env}

/** A node's examples run against its promise (`Denote` of the post), its code under the examples' givens
  * (`Values.within`), and, for a proven flow, on the implementations (`run`).
  */
final class Examples[F[_]: Sync](denote: Denote, run: FlowInterpreter[F]):
  def of(r: Resolved, node: NodeId): F[List[ExampleResult]] = r.theory.node(node).map(_.statement) match
    case Some(Statement.Contract(_, p, _))        => calls(r, node, p)
    case Some(Statement.AssumedCall(_, p))        => calls(r, node, p)
    case Some(Statement.FlowContract(_, p, _, _)) =>
      p.examples.zipWithIndex.traverse((e, i) => onImplementations(r, node, e).map(ExampleResult(i, onModels(e), _)))
    case _                                        => Sync[F].pure(Nil)

  /** Each call against the promise, and against the code attached to the operation (a contract's code, or the
    * adapter an assumption's operation runs as) under the example's givens.
    */
  private def calls(r: Resolved, node: NodeId, p: Promise[CallExample]): F[List[ExampleResult]] = Sync[F].delay {
    CallCheck.of(denote, r.theory, node).toList.flatMap { check =>
      val givens = Givens.of(denote, r.theory)
      val code = r.theory.code.attached.get(node).flatMap(_.code.scala)
      val onCode = code.map(c => CodeExamples(denote, givens, check, c.impl).of(p.examples))
      PromiseExamples(denote, givens, Assumes.of(denote, r.theory), check).of(p.examples).zipWithIndex
        .map((onPromise, i) => ExampleResult(i, onPromise, onCode.map(_(i))))
    }
  }

  /** The post of the run on the models from the example's world. */
  private def onModels(e: RunExample): Agreement = ???

  /** The proven flow run on the implementations from the example's inputs, its result against the example's. */
  private def onImplementations(r: Resolved, node: NodeId, e: RunExample): F[Option[Agreement]] =
    steps(r, node).traverse { (params, prog, ty) =>
      val start = params.zip(e.inputs).foldLeft(Env.inForce)((en, xv) =>
        en.bind(xv._1.id, denote.literal(xv._2, xv._1.ty)))
      run.prog(prog, start).map(v => returned(e.end, denote.reflect(v, ty)))
    }

  /** The proven flow's parameters, steps and result type. */
  private def steps(r: Resolved, node: NodeId): Option[(List[Binder], Prog, Ty)] =
    for
      d     <- r.theory.code.attached.get(node).flatMap(_.code.proven).flatMap(r.theory.vocabulary.define)
      steps <- d.lambda.body match
                 case Expr.Do(p, Ty.FlowOf(t)) => Some((d.lambda.params, p, t))
                 case _                        => None
    yield steps

  private def returned(end: RunEnd, got: Value): Agreement = end match
    case RunEnd.Returns(v, _) if v == got => Agreement.Agrees
    case _                                => Agreement.Returned(got)
