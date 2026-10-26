package frflow.runtime

import frflow.core.analysis.{Choice, Fixed, InForce, Resolve}
import frflow.core.code.Code
import frflow.core.expr.{Exprs, Lambda}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Fixing, Statement}
import frflow.core.Theory
import frflow.dsl.node.Binding
import frflow.eval.{Applied, Denote}

/** The values a service runs with: what is wired (the bindings given, the other operations' services) over the
  * definitions in force (the first listed); everything the contract needs bound, or `Unbound` when it is wired, not
  * on the first call.
  */
object Wiring:
  def values(denote: Denote, t: Theory, contract: NodeId, wired: Map[SymbolName, () => Any])
      : Either[WiringError, Map[SymbolName, () => Any]] =
    val all = definitions(denote, t) ++ wired
    val missing = needed(t, contract).filterNot(all.contains)
    Either.cond(missing.isEmpty, all, WiringError.Unbound(contract, missing))

  /** The bindings given: a value read when the code reads it, a table as its entries. */
  def bound(bindings: List[Binding]): Map[SymbolName, () => Any] = bindings.map {
    case Binding.Value(s, v)  => s -> v
    case Binding.Table(s, es) => s -> (() => es)
  }.toMap

  /** Each symbol a definition in force fixes, computed by its term under the values in force where it is read. */
  def definitions(denote: Denote, t: Theory): Map[SymbolName, () => Any] =
    InForce.of(t, Choice.FirstListed).fixedBy.toList.flatMap {
      case (Fixed.Term(s), d) => term(t, d, s).map(l => s -> computed(denote.lambda(l)))
      case _                  => None
    }.toMap

  private def term(t: Theory, definition: NodeId, s: SymbolName): Option[Lambda] =
    t.node(definition).map(_.statement).collect { case Statement.Definition(fs) => fs.toList }.toList.flatten
      .collectFirst { case Fixing.TermAs(`s`, as) => as.value }

  private def computed(term: Applied): () => Any = () => term.called(Nil).unwrap

  /** As today's `needed`: what its promise reads (itself or through the defines it calls), what its examples give
    * values to, and what its code calls; not its own operation.
    */
  private def needed(t: Theory, contract: NodeId): List[SymbolName] =
    val own = t.node(contract).flatMap(_.statement.operation)
    val examples = t.node(contract).toList.flatMap(_.statement.givens.map(_.symbol))
    (Resolve.mentions(t, contract).symbols ++ examples ++ reads(t, contract)).distinct.filterNot(own.contains)

  /** What its code reads: the operations plain code calls, as attached; a define run as Scala, what it mentions. */
  private def reads(t: Theory, contract: NodeId): List[SymbolName] = t.code.attached.get(contract).map(_.code) match
    case Some(Code.Tested(_, calls)) => calls
    case Some(c)                     =>
      t.vocabulary.closure(c.proven.toList).flatMap(d => Exprs.mentions(d.lambda.body).symbols)
    case None                        => Nil
