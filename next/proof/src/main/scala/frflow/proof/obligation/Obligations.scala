package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.analysis.outside.{Premises, Reads}
import frflow.core.graph.Walk
import frflow.core.name.{LeanNames, NodeId, SymbolName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.ty.Ty
import frflow.proof.obligation.ObligationName.*
import frflow.proof.obligation.tried.Tries
import frflow.proof.terms.{CallingCode, TermTable}

/** What Lean is asked of each node (docs/DAG.md §3): a function of the resolved theory and of the obligations the
  * proof files prove. What is asked of the theory as a whole is `Joint`'s and `ExampleGoals`'.
  */
object Obligations:
  def of(r: Resolved, table: TermTable, authored: Set[(NodeId, ObligationName)]): List[NodeObligations] =
    r.theory.refinement.nodes.filter(_.statement.stated).map { n =>
      NodeObligations(n.id, Required.of(r, authored, n.id), Tries.of(r, table, n.id))
    } ++ r.theory.refinement.nodes.filterNot(_.statement.stated).flatMap(n =>
      Option(Tries.frozen(r, n.id)).filter(_.nonEmpty).map(NodeObligations(n.id, Nil, _)))

  /** The rules an obligation of `n` takes as given where it is stated: the guards its variables and its worlds come
    * with (`Guarded`), read as each kind is built, one case per kind, so a new kind must say what it takes (the step
    * 13d third pass's R3-B1). A statement is kept only as every rule its obligations take is (`ReadProof.kept`).
    */
  def takes(r: Resolved, n: NodeId, o: ObligationName): List[NodeId] = (o match
    // the node's claim as `def claim` states it (`Lowering.guards`): its variables, its isConstant's equations over
    // each writer's inputs, the worlds it reads, and the defines' `forall`s it reads through; of `root_impl`, the
    // roots' claims together, each its own guards: of this root, its claim's
    case Impl                       => Reads.taken(r.theory, n)
    // and what always holds of each value provided where the code of a part, or of a leaf below, runs: an open term
    // of the step (`Lowering.provided`, `LowerProp.Values`; the step 13d fourth pass's P4-N1)
    case Complete | Feasible        => Reads.taken(r.theory, n) ++ provided(r, r.theory.refinement.parts(n))
    case RootImpl                   => Reads.taken(r.theory, n) ++ provided(r, Walk.breadthFirst(
        r.theory.refinement.parts(n), identity)(r.theory.refinement.parts))
    // the assumptions of `always` on the values from outside (`Made.outside`)
    case Outside                    => Reads.rulesAt(r.theory, Premises.fromOutside(r.theory), Nil)
        .filter(a => r.theory.node(a).exists(_.statement.kind == NodeKind.Assumption))
    // the run's inputs and the world it starts from (`Required.keeps`, `Required.outside`)
    case Cover(op)                  => Reads.coverTaken(r.theory, SymbolName(op))
    // the maker's inputs and world (`Made.of`), or the calling code's (`Made.atCalls`)
    case Made(maker)                => made(r, maker)
    // two steps' runs from any world, no guard (`LowerCommute`); a try refutes, nothing is proven from it; a start
    // from the `initially`s, assumptions; a witness, a group's or an example's values, none taken
    case Commute(_) | Tried(_) | Start(_) | Inhabited(_) | Consistent(_) | Satisfiable(_, _) | Example(_) => Nil
  ).filterNot(_ == n)

  /** The rules on the values provided where the code of `ns` runs, which each of their claims mentions. */
  private def provided(r: Resolved, ns: List[NodeId]): List[NodeId] =
    Reads.rulesAt(r.theory, ns.flatMap(Reads.provided(r.theory, _)).map(_._2), Nil)

  /** `made_<maker>`: a store's operation on its model's world and its inputs (`Making.ofModel`), a define's inputs, a
    * program's and the world of the stores it reads (`Making.ofDefine`, `ofProgram`); `made_<code>_call_<i>`: the
    * calling code's inputs and world, and every value rule on what its steps bind (`CallSites`).
    */
  private def made(r: Resolved, maker: String): List[NodeId] =
    val t = r.theory
    val calling = if maker.contains("_call_") then CallingCode.of(t).find(c =>
      c.calls.indices.exists(LeanNames.call(c.code, _) == maker)) else None
    calling.fold {
      val op = SymbolName(maker)
      t.vocabulary.modelOf(op).fold(Reads.rulesAt(t, Reads.inputs(t, op), Reads.ofProgram(t, op)))(m =>
        Reads.rulesAt(t, m.sigOf(op).toList.flatMap(_.params.map(_._2)), List(m.name)))
    } { c =>
      val values = t.nodes.map(_.node).filter(x => x.statement.rule && x.statement.range.exists {
        case Range.Made(ty) => ty != Ty.World
        case _              => false
      }).map(_.id)
      Reads.rulesAt(t, Reads.inputs(t, c.definition), Reads.ofProgram(t, c.definition)) ++ values
    }
