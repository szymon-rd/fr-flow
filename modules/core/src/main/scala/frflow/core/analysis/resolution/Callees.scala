package frflow.core.analysis.resolution

import cats.syntax.all.*
import frflow.core.expr.{Exprs, Mentions}
import frflow.core.graph.Walk
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.Theory

/** The proven code of the Definitions a statement mentions: what stands for each when the statement is asked of the
  * code (the define itself; a statement relating two Definitions asks both at once), and what that code calls,
  * through the defines it calls.
  */
final case class Callees(standsFor: Map[SymbolName, DefName], calls: Mentions)

object Callees:
  def of(t: Theory, id: NodeId): Option[Callees] =
    Constrained.of(t, id).flatMap(op => ofDefinition(t, op).toList).reduceOption((a, b) =>
      Callees(a.standsFor ++ b.standsFor, a.calls |+| b.calls))

  /** One Definition's proven code. */
  def ofDefinition(t: Theory, op: SymbolName): Option[Callees] =
    t.code.attached.get(op).flatMap(_.code.proven).map(d => Callees(Map(op -> d), calls(t, d)))

  /** A Definition's proven code and the proven code of everything it reaches (`reaching`), each standing for its
    * Definition: what a `cover_` puts in, as `impl` does.
    */
  def within(t: Theory, op: SymbolName): Callees =
    reaching(t, List(op)).flatMap(ofDefinition(t, _).toList).foldLeft(Callees(Map.empty, Mentions.empty))((a, b) =>
      Callees(a.standsFor ++ b.standsFor, a.calls |+| b.calls))

  /** `ss` and every Definition the proven code standing for them reaches, through the code standing for each
    * Definition it calls in turn: what a statement asked of the code is about, all the way down.
    */
  def reaching(t: Theory, ss: List[SymbolName]): List[SymbolName] =
    Walk.breadthFirst(ss, identity)(s => ofDefinition(t, s).toList.flatMap(_.calls.symbols))

  /** The Definitions a define calls, through the defines it calls. */
  def calledBy(t: Theory, d: DefName): List[SymbolName] = calls(t, d).symbols

  private def calls(t: Theory, d: DefName): Mentions =
    t.vocabulary.closure(List(d)).foldMap(x => Exprs.mentions(x.lambda.body))
