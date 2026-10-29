package frflow.proof.layout

import cats.data.NonEmptyList
import frflow.core.analysis.{Callees, Resolved}
import frflow.core.name.{LeanNames, NodeId, SymbolName}
import frflow.core.spec.Range
import frflow.proof.lean.ast.*
import frflow.proof.obligation.{Hyp, Prop, Substitute}
import frflow.proof.terms.TermTable

/** `RootImpl.lean`: `root_impl`, each root resting on proven code holds of that code (every Definition with proven
  * code standing as it, `σ`), from what it trusts only: the leaves below it no proven code stands for. Composed from
  * every node's `holds` and every proven implementation's `impl` (`Composition`); several roots are proven together.
  */
object RootImplModule:
  def of(r: Resolved, table: TermTable): Option[LeanModule] = of(Lowering(r, table))

  /** The roots `root_impl` states: each stated over every possible value, resting, through its parts, on proven
    * code.
    */
  def roots(l: Lowering): List[NodeId] =
    val c = Composition(l)
    def reaches(n: NodeId): Boolean = c.coded(n) || (c.composed(n) && c.leaves(n).exists(reaches))
    l.resolved.theory.refinement.roots.filter(n => n.statement.stated && n.statement.range.contains(Range.Possible))
      .map(_.id).filter(reaches)

  def of(l: Lowering): Option[LeanModule] =
    val c = Composition(l)
    val σ = code(l)
    NonEmptyList.fromList(roots(l)).map { rs =>
      val statements = rs.map(n => n -> statement(l, c, σ, n))
      val proofs = statements.map((n, s) => Params.lambda(Params.of(l.props.statement(s),
        c.trusted(n).map(x => LeanNames.hypothesis(x))), c.proven(n, σ)))
      val stated = if rs.size == 1 then statements.head._2 else Prop.Both(statements.map(_._2))
      val proof = if rs.size == 1 then proofs.head else LExpr.Anonymous(proofs.toList)
      val name = Names.builtin("root_impl")
      val decls = List(Decl.Documented(s"${rs.toList.map(_.value).mkString(", ")} hold of the code, from what is " +
        "trusted.", Decl.Theorem(Nil, name, Nil, l.props.statement(stated), Proof.Below(proof), Break.SameLine)),
        Decl.PrintAxioms(Names.path(l.kb.value, "RootImpl", "root_impl")))
      Imports.onto(l, LeanModule(l.layout.rootImpl, Nil, Preamble.generated, Names.path(l.kb.value, "RootImpl"), Nil,
        decls))
    }

  /** `∀ U, h_T₁ → … → root[σ]`: over every open term the composition names. */
  private def statement(l: Lowering, c: Composition, σ: Map[SymbolName, Substitute], n: NodeId): Prop =
    val extra = c.involved(n).flatMap(p => l.props.opens(p).symbols).distinct.filterNot(σ.contains)
    val trusted = c.trusted(n).map(x => Hyp(LeanNames.hypothesis(x), Prop.ClaimOf(x, σ)))
    Prop.Forall(Nil, Prop.ForEvery(extra, Prop.Implies(trusted, Prop.ClaimOf(n, σ))))

  /** Each Definition with proven code, standing as that code. */
  private def code(l: Lowering): Map[SymbolName, Substitute] =
    val t = l.resolved.theory
    t.code.attached.keys.toList.flatMap(s =>
      Callees.ofDefinition(t, s).flatMap(_.standsFor.get(s)).map(s -> Substitute.Code(_))).toMap
