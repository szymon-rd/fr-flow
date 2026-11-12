package frflow.core.analysis.outside

import frflow.core.analysis.resolution.{Callees, SaysWhat}
import frflow.core.code.Code
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** What about the world outside a statement's check rests on (owner §16, §21), derived from the statement and the
  * code, each to be listed by the statement's `.assuming` (owner §15: the one mechanism; `Validate` checks the list,
  * `PremiseMissing`, `PremiseNotNeeded`): of every claim, what values from outside meet, each assumption of
  * `always[U]` whose guard the claim's form or its `made_`/`cover_` obligations carry (on a variable it quantifies
  * over, an input of a maker it is asked of, or a value provided where the code runs that it mentions;
  * `Guards.applies` decides, as it does for the guards the prover states). An `always[T]` claim also rests on what
  * `T`s from outside meet when an entry Definition's input or a value provided where the code runs can hold one,
  * whether or not an assumption says it: no covered code makes those.
  */
object Premises:
  def of(t: Theory, id: NodeId): List[Premise] =
    t.node(id).filter(n => n.statement.kind == NodeKind.Claim && !SaysWhat.is(t, n.id)).toList.flatMap(n =>
      n.statement.range.toList.flatMap {
        case Range.Possible => Nil
        case Range.Made(ty) => passed(t, ty)
      } ++ guarded(t, n)).distinct

  /** The Definitions with code that no code of another calls: where values enter from outside. */
  def entries(t: Theory): List[SymbolName] =
    val called = t.code.attached.values.toList.flatMap(a => a.code match
      case Code.Tested(_, cs) => cs
      case c                  => c.proven.toList.flatMap(d => Callees.calledBy(t, d)))
    t.code.attached.keys.toList.filterNot(called.contains)

  /** What `ty`s from outside meet, when values from outside can hold one. */
  private def passed(t: Theory, ty: Ty): List[Premise] =
    Option.when(fromOutside(t).exists(Guards.applies(t, ty, _)))(Premise.FromOutside(ty)).toList

  /** The types of the values that enter from outside: an entry Definition's inputs and the values provided where the
    * code runs.
    */
  def fromOutside(t: Theory): List[Ty] = (entries(t).flatMap(Reads.inputs(t, _)) ++ provided(t)).distinct

  /** What values from outside meet, of each type an assumption of `always` is about whose guard the node carries:
    * on what it quantifies over, and on the inputs of what its `cover_` and `made_` are asked of.
    */
  private def guarded(t: Theory, n: Node): List[Premise] =
    val values = Reads.quantified(n) ++ Reads.provided(t, n.id).map(_._2) ++
      Scope.of(t, n.id).flatMap(Reads.inputs(t, _))
    t.nodes.map(_.node).filter(a => a.id != n.id && a.statement.kind == NodeKind.Assumption)
      .flatMap(_.statement.range).collect {
        case Range.Made(u) if values.exists(Guards.applies(t, u, _)) => Premise.FromOutside(u)
      }

  /** The types of the values provided where the code runs. */
  private def provided(t: Theory): List[Ty] = t.code.attached.toList.collect {
    case (s, a) if a.code == Code.Provided => t.vocabulary.symbol(s).map(_.ty)
  }.flatten.collect { case SymbolType.Typed(ty) => ty }
