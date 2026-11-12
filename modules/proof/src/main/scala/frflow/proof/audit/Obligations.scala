package frflow.proof.audit

import frflow.core.analysis.outside.{Premises, Reads}
import frflow.core.analysis.resolution.Resolved
import frflow.core.graph.Walk
import frflow.core.name.{LeanNames, NodeId, SymbolName}
import frflow.core.spec.{NodeKind, Range}
import frflow.proof.obligation.{NodeObligations, ObligationName, Required}
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
    }

  /** The rules an obligation of `n` takes as given where it is stated: the guards its variables come with (`Guarded`),
    * read as each kind is built, one case per kind, so a new kind must say what it takes. A statement is kept only as
    * every rule its obligations take is (`ReadProof.kept`).
    */
  def takes(r: Resolved, n: NodeId, o: ObligationName): List[NodeId] = (o match
    // the node's claim as `def claim` states it (`Lowering.guards`): its variables, and the defines' `forall`s it
    // reads through; of `root_impl`, the roots' claims together, each its own guards: of this root, its claim's
    case Impl                       => Reads.taken(r.theory, n)
    // and what always holds of each value provided where the code of a part, or of a leaf below, runs: an open term
    // of the step (`Lowering.provided`, `LowerProp.Values`)
    case Complete | Feasible        => Reads.taken(r.theory, n) ++ provided(r, r.theory.refinement.parts(n))
    case RootImpl                   => Reads.taken(r.theory, n) ++ provided(r, Walk.breadthFirst(
        r.theory.refinement.parts(n), identity)(r.theory.refinement.parts))
    // the assumptions of `always` on the values from outside (`Made.outside`)
    case Outside                    => Reads.rulesAt(r.theory, Premises.fromOutside(r.theory))
        .filter(a => r.theory.node(a).exists(_.statement.kind == NodeKind.Assumption))
    // the maker's inputs (`Made.of`), or the calling code's (`Made.atCalls`)
    case Made(maker)                => made(r, maker)
    // none: a try; a witness; an example
    case Tried(_) | Inhabited(_) | Consistent(_) | Satisfiable(_, _) | Example(_, _) | ExampleOpposite(_, _) => Nil
  ).filterNot(_ == n)

  /** The rules on the values provided where the code of `ns` runs, which each of their claims mentions. */
  private def provided(r: Resolved, ns: List[NodeId]): List[NodeId] =
    Reads.rulesAt(r.theory, ns.flatMap(Reads.provided(r.theory, _)).map(_._2))

  /** `made_<maker>`: a define's inputs (`Making.ofDefine`); `made_<code>_call_<i>`: the calling code's inputs, and
    * every value rule on what it binds.
    */
  private def made(r: Resolved, maker: String): List[NodeId] =
    val t = r.theory
    val calling = if maker.contains("_call_") then CallingCode.of(t).find(c =>
      c.calls.indices.exists(LeanNames.call(c.code, _) == maker)) else None
    calling.fold(Reads.coverTaken(t, SymbolName(maker))) { c =>
      val values = t.nodes.map(_.node).filter(x => x.statement.rule && x.statement.range.exists {
        case Range.Made(_) => true
        case _             => false
      }).map(_.id)
      Reads.coverTaken(t, c.definition) ++ values
    }
