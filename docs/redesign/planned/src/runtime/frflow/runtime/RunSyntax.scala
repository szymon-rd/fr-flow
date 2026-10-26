package frflow.runtime

import cats.effect.Sync
import cats.syntax.all.*
import frflow.core.spec.Statement
import frflow.dsl.flow.{Bound, Flow}
import frflow.dsl.kb.KnowledgeBase
import frflow.dsl.node.{Binding, Node}

/** `knowledge.service(c)(bindings*)` and `knowledge.run[F](job)(bound*)`, as models and applications write them: the
  * knowledge base elaborated once (`kb.elaborated`), wired with the default reporter; a wiring error thrown here.
  */
object RunSyntax:
  extension (kb: KnowledgeBase)
    def service[F](contract: Node[Statement.Contract, F])(bindings: Binding*): F =
      kb.elaborated.toEither.leftMap(es => s"${kb.name}: ${es.toList.mkString("; ")}")
        .flatMap(Running(_, Reporter.log).service(contract)(bindings*).leftMap(_.toString))
        .fold(why => throw IllegalStateException(s"FrFlow: $why"), identity)
    /** The flow's code run in `F` against the implementations bound (`eval.run.FlowRun.sequential`), as today. */
    def run[F[_]: Sync, A, R](job: Node[Statement.FlowContract, A => Flow[R]])(bound: Bound*): A => F[R] = ???
