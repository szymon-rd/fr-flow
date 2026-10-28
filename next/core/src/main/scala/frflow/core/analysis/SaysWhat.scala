package frflow.core.analysis

import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.Theory

/** The claims saying what a Declaration is (2.7): at the bottom (no parts, its rules aside), over every possible
  * value, mentioning a Declaration. Such a claim is the Declaration's meaning: the proven code stands in it for the
  * Definitions it mentions, its consistency group shows some meaning meets it, and nothing is proven of the code from
  * it, so it is asked no `impl` and rests on no premise. Derived, not a kind: an ordinary claim.
  */
object SaysWhat:
  /** The Declarations a claim says what they are; none when it is no such claim. */
  def declarations(t: Theory, id: NodeId): List[SymbolName] =
    t.node(id).filter(n => n.statement.kind == NodeKind.Claim && n.statement.range.contains(Range.Possible) &&
      t.refinement.parts(id).isEmpty).toList.flatMap(_ => Constrained.of(t, id).filter(Constrained.isDeclaration(t, _)))

  def is(t: Theory, id: NodeId): Boolean = declarations(t, id).nonEmpty

  /** The proven code a statement is checked against (`impl`): none for a claim saying what a Declaration is, where the
    * code only stands in it.
    */
  def checkedAgainst(t: Theory, id: NodeId): Option[Callees] = Option.when(!is(t, id))(Callees.of(t, id)).flatten
