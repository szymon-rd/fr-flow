package frflow.core.analysis

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.{Elaborated, Theory}
import frflow.core.code.Code
import frflow.core.graph.Edge
import frflow.core.name.SymbolName
import frflow.core.spec.{Node, NodeKind, Range}

/** The structure rules (docs/DAG.md §2) as one pure function: every problem at once, or the theory as `Valid`. */
object Validate:
  def apply(e: Elaborated): ValidatedNec[Problem, Valid] =
    val t = e.theory
    (structure(t), vocabulary(t), outside(t), code(t), Meanings.problems(t)).mapN((_, _, _, _, _) => Valid(e))

  private def all(ps: List[Problem]): ValidatedNec[Problem, Unit] =
    NonEmptyChain.fromSeq(ps).fold(Validated.validNec(()))(Validated.invalid)

  /** Acyclic, every edge inside the graph, at least one root statement (several are allowed, owner §11). */
  private def structure(t: Theory): ValidatedNec[Problem, Unit] =
    val r = t.refinement
    val ids = t.nodes.map(_.node.id)
    all(ids.diff(ids.distinct).distinct.map(Problem.DuplicateId(_)) ++
      Option.when(r.roots.isEmpty && t.nodes.nonEmpty)(Problem.NoRoot) ++
      r.nodes.filter(n => r.ancestors(n.id).contains(n.id)).map(n => Problem.AboveItself(n.id)) ++
      r.nodes.flatMap(n => r.parents(n.id).filterNot(ids.contains).map(Problem.ParentOutside(n.id, _))) ++
      r.nodes.collect { case n if n.statement.kind == NodeKind.Design && r.parents(n.id).isEmpty =>
        Problem.DesignWithoutParent(n.id) } ++
      underDesign(t) ++ premises(t))

  /** What a node assumes is an assumption or an `always`; a fact about the outside is assumed, and never a part. */
  private def premises(t: Theory): List[Problem] =
    t.edges.collect {
      case Edge.Assumes(n, p) if !t.node(p).exists(premise) => Problem.PremiseNotAssumed(n, p)
      case Edge.PartOf(p, w) if t.node(p).flatMap(_.statement.outside).nonEmpty => Problem.OutsideAsPart(p, w)
    } ++ t.nodes.map(_.node).collect {
      case n if n.statement.kind == NodeKind.Claim && n.statement.outside.nonEmpty => Problem.OutsideClaimed(n.id)
    }

  private def premise(n: Node): Boolean =
    n.statement.kind == NodeKind.Assumption || n.statement.range.exists(_ != Range.Possible)

  private def underDesign(t: Theory): List[Problem] =
    for
      n <- t.refinement.nodes
      p <- t.refinement.parents(n.id).flatMap(t.refinement.node)
      if p.statement.kind == NodeKind.Design && n.statement.kind != NodeKind.Design
    yield Problem.UnderDesign(n.id, p.id)

  /** Each name declared once, none a name generated Lean binds itself, and no statement mentioning a value with no
    * Lean type. A model's namespace in Lean is its name capitalized (`Stored`), so it is declared there too: a model
    * named as its boundary's class (`shelf` of `Shelf`) is declared twice.
    */
  private def vocabulary(t: Theory): ValidatedNec[Problem, Unit] =
    val v = t.vocabulary
    val names = v.sorts.map(_.name.value) ++ v.types.map(_.typeName.value) ++ v.symbols.map(_.name.value) ++
      v.defines.map(_.name.value) ++ v.boundaries.map(_.className) ++ v.models.map(_.name.value.capitalize)
    all(names.filter(Reserved.names).distinct.map(Problem.ReservedName(_)) ++
      names.diff(names.distinct).distinct.map(Problem.DeclaredTwice(_)) ++
      t.nodes.map(_.node.id).flatMap(id => Constrained.of(t, id).filter(Constrained.isCodeOnly(t, _))
        .map(Problem.CodeOnlyInStatement(id, _))))

  /** A statement's `.assuming` lists exactly the facts about the outside its check rests on (`Premises`: derived,
    * and only checked), every program writing a store is among those the outside lets write it, and every `always[T]`
    * reaches each `T` covered code can make (`Unreached`).
    */
  private def outside(t: Theory): ValidatedNec[Problem, Unit] =
    val missing = t.nodes.map(_.node.id).flatMap(id => Premises.of(t, id)
      .filter(Outsides.assumed(t, id, _).isEmpty).map(p => Problem.PremiseMissing(id, p, Outsides.saying(t, p))))
    val unneeded = t.nodes.map(_.node.id).flatMap(id => Outsides.premises(t, id).filter(p =>
      t.node(p).exists(n => Outsides.aboutOutside(n) && !Premises.of(t, id).exists(Outsides.saysOf(n, _))))
      .map(Problem.PremiseNotNeeded(id, _)))
    val unlisted = t.vocabulary.models.flatMap(m => Outsides.saying(t, Premise.WrittenOnlyBy(m.name)).toList
      .flatMap(_ => Premises.writers(t, m).filterNot(Outsides.writers(t, m.name).contains))
      .map(Problem.WriterNotListed(m.name, _)))
    all(missing ++ unneeded ++ unlisted ++ Unreached.of(t))

  /** Code is for a Definition some statement mentions (a provided one with no Lean type is read by plain code only);
    * a node checked against proven code has as parts only statements about what the code calls (`impl` proves it
    * from them: docs/DAG.md §3); the models it is proven on are premises, not parts.
    */
  private def code(t: Theory): ValidatedNec[Problem, Unit] =
    val unclaimed = t.code.attached.toList.collect {
      case (s, a) if !providedToCode(t, s, a.code) && Constrained.statements(t, s).isEmpty => s
    }
    all(unclaimed.map(Problem.CodeWithoutClaim(_)) ++ t.nodes.map(_.node.id).flatMap(id =>
      Callees.of(t, id).toList.flatMap(c => t.refinement.parts(id).filterNot(c.about(t, _))
        .map(Problem.PartNotCalled(id, _)))))

  /** A value with no Lean type, provided where the code runs (a connection): no statement can mention it. */
  private def providedToCode(t: Theory, s: SymbolName, c: Code): Boolean =
    Constrained.isCodeOnly(t, s) && c == Code.Provided
