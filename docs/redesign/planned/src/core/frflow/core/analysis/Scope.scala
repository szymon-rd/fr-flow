package frflow.core.analysis

import frflow.core.graph.Edge
import frflow.core.name.{NodeId, TypeName}
import frflow.core.spec.{Node, Statement}
import frflow.core.Theory
import frflow.core.ty.Ty

/** The nodes an invariant applies to (docs/DAG.md §2), within the nodes it names as its scope: the contracts whose
  * result can hold what its rule is about, and the designs governing code no proof below the rule covers. A type
  * holds what the rule is about when it names that type or a type whose fields hold it.
  */
object Scope:
  def of(t: Theory, invariant: NodeId): List[NodeId] =
    t.node(invariant).map(_.statement).collect { case Statement.Invariant(rule, scope) =>
      val about = rule.value.params.lift(1).flatMap(x => Ty.names(x.ty).headOption)
      t.refinement.nodes.filter(c => within(t, scope, c.id) && applies(t, invariant, about, c)).map(_.id)
    }.getOrElse(Nil)

  private def within(t: Theory, scope: List[NodeId], c: NodeId): Boolean =
    scope.isEmpty || (c :: t.refinement.ancestors(c)).exists(scope.contains)

  private def applies(t: Theory, invariant: NodeId, about: Option[TypeName], c: Node): Boolean = c.statement match
    case Statement.Contract(_, p, _)        => returns(t, about, p.post.value.params.lastOption.map(_.ty))
    case Statement.FlowContract(_, p, _, _) => returns(t, about, p.post.value.params.lastOption.map(_.ty))
    case Statement.Design(_)                =>
      val contracts = t.refinement.ancestors(c.id).flatMap(t.node).filter(isContract)
      contracts.isEmpty || contracts.exists(a => answers(t, invariant, a.id) || applies(t, invariant, about, a))
    case _                                  => false

  private def returns(t: Theory, about: Option[TypeName], result: Option[Ty]): Boolean =
    result.forall(r => about.forall(holds(t, _, r, Set.empty)))

  private def holds(t: Theory, about: TypeName, ty: Ty, seen: Set[TypeName]): Boolean =
    val names = Ty.names(ty)
    names.contains(about) || names.filterNot(seen).exists(n =>
      t.vocabulary.dataType(n).exists(_.fieldTypes.exists(holds(t, about, _, seen + n))))

  /** `c` keeps the invariant or is exempt from it. */
  def answers(t: Theory, invariant: NodeId, c: NodeId): Boolean = t.edges.exists {
    case Edge.Keeps(`c`, `invariant`, _)  => true
    case Edge.Exempt(`c`, `invariant`, _) => true
    case _                                => false
  }

  private def isContract(n: Node): Boolean = n.statement match
    case Statement.Contract(_, _, _) | Statement.FlowContract(_, _, _, _) => true
    case _                                                                => false
