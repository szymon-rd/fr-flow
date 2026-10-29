package frflow.core.analysis

import frflow.core.code.Code
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.Theory

/** The claims saying what a Declaration is (2.5, 2.7): below a statement over it, at the bottom (no parts, its rules
  * aside), over every possible value, mentioning a Declaration. A root mentioning one is a purpose not refined yet,
  * not checked by anything. Such a claim is the Declaration's meaning: the proven code stands in it for the
  * Definitions it mentions, its consistency group shows some meaning meets it, and nothing is proven of the code from
  * it, so it is asked no `impl` and rests on no premise. Derived, not a kind: an ordinary claim.
  */
object SaysWhat:
  /** The Declarations a claim says what they are; none when it is no such claim. */
  def declarations(t: Theory, id: NodeId): List[SymbolName] =
    t.node(id).filter(n => n.statement.kind == NodeKind.Claim && n.statement.range.contains(Range.Possible) &&
      t.refinement.parents(id).nonEmpty && t.refinement.parts(id).isEmpty).toList
      .flatMap(_ => Constrained.of(t, id).filter(Constrained.isDeclaration(t, _)))

  def is(t: Theory, id: NodeId): Boolean = declarations(t, id).nonEmpty

  /** The proven code a claim is checked against (`impl`): none for a claim saying what a Declaration is, where the
    * code only stands in it, nor for an assumption mentioning a value the code does not give (an open one, or one
    * provided where the code runs), which is trusted with the code standing in it and held by its group or as a
    * premise. An assumption every word of which the code gives a meaning is a statement about the code itself, and
    * proven of it as a claim is: nothing else would check it.
    */
  def checkedAgainst(t: Theory, id: NodeId): Option[Callees] =
    Option.when(!is(t, id) && t.node(id).exists(n => n.statement.kind == NodeKind.Claim || ofCode(t, n)))(
      Callees.of(t, id)).flatten

  /** An assumption over every possible value, each Definition it mentions, and each the code standing in it reaches,
    * with proven code or a fixed value.
    */
  private def ofCode(t: Theory, n: Node): Boolean =
    val words = Callees.reaching(t, Constrained.of(t, n.id))
    n.statement.kind == NodeKind.Assumption && n.statement.range.contains(Range.Possible) && !n.statement.rule &&
      n.statement.said.nonEmpty && words.nonEmpty && words.forall(s => !Constrained.isDeclaration(t, s) &&
        t.code.attached.get(s).exists(a => a.code.proven.nonEmpty || (a.code match
          case Code.Valued(_) | Code.Modelled(_) => true
          case _                                 => false)))
