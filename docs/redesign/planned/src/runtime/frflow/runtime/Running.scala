package frflow.runtime

import cats.syntax.all.*
import frflow.core.code.{Code, Impl}
import frflow.core.Elaborated
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.Statement
import frflow.dsl.node.{Binding, Node}
import frflow.eval.Denote
import frflow.eval.run.{Assumes, CallCheck}
import frflow.runtime.check.{AssumptionWatch, Sampling}

/** A knowledge base wired into a running system: `service(c)(bindings*)` is the contract's code as a plain function,
  * checked as `Policy` says, every wiring mistake found here rather than on a call.
  */
final class Running(e: Elaborated, reporter: Reporter):
  private val denote = Denote(e)
  private val t = e.theory

  def service[F](contract: Node[Statement.Contract, F])(bindings: Binding*): Either[WiringError, F] =
    wired(contract.head.id, bindings.toList).map(_.as[F])

  /** The contract's service, untyped: what `service` types, and what calls of its operation from other code reach. */
  def wired(contract: NodeId, bindings: List[Binding]): Either[WiringError, Service] =
    for
      attached <- t.code.attached.get(contract).toRight(WiringError.NoCode(contract))
      code     <- runs(attached.code).toRight(WiringError.NoCode(contract))
      check    <- CallCheck.of(denote, t, contract).toRight(WiringError.NotAContract(contract))
      values   <- Wiring.values(denote, t, contract, operations(contract, bindings) ++ Wiring.bound(bindings))
      watch    <- AssumptionWatch.of(assumed(Wiring.bound(bindings).keySet), values)
                    .leftMap(WiringError.AssumptionBroken(_))
    yield Service(Guard(contract, check, Sampling.of(Policy.of(attached)), watch), code, values, reporter)

  /** The facts that read only symbols the developer bound, as today. */
  private def assumed(bound: Set[SymbolName]): List[Assumes] = Assumes.of(denote, t).filter(_.within(bound))

  /** Plain code, or a proven define run as Scala. */
  private def runs(code: Code): Option[Impl] = code.scala.map(_.impl).orElse(code.proven.flatMap(denote.impl))

  /** Each other operation a plain call reaches whose node has code, the first listed: a contract's code, or the
    * adapter of an assumption about an outside system's operation. Each is its service, checked on its own calls and
    * wired when first called, as today (a wiring mistake there is thrown then).
    */
  private def operations(contract: NodeId, bindings: List[Binding]): Map[SymbolName, () => Any] =
    val own = t.node(contract).flatMap(_.statement.operation)
    val coded = t.nodes.map(_.node).filter(n => called(n.statement) && t.code.attached.contains(n.id))
      .flatMap(n => n.statement.operation.map(_ -> n.id)).filterNot((op, _) => own.contains(op))
    coded.distinctBy(_._1).map((op, c) => op -> later(c, bindings)).toMap

  /** A node on an operation plain code calls (a flow's runs through `run`). */
  private def called(s: Statement): Boolean = s match
    case Statement.Contract(_, _, _) | Statement.AssumedCall(_, _) => true
    case _                                                        => false

  private def later(contract: NodeId, bindings: List[Binding]): () => Any =
    lazy val f = wired(contract, bindings).fold(err => throw IllegalStateException(s"FrFlow: $err"), _.as[AnyRef])
    () => f
