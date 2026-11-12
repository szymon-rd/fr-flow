package frflow.core.analysis

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.analysis.{Bounded, Unreached}
import frflow.core.analysis.outside.{Outsides, Premises}
import frflow.core.analysis.resolution.{Constrained, Resolve, Valid}
import frflow.core.code.Code
import frflow.core.{Elaborated, Theory}
import frflow.core.graph.{Edge, Walk}
import frflow.core.name.{LeanNames, SymbolName}
import frflow.core.spec.NodeKind

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
      underDesign(t) ++ premises(t) ++ below(t))

  /** Each premise resting on the node that assumes it: the parents and premises above it reach the node. */
  private def below(t: Theory): List[Problem] =
    val r = t.refinement
    t.edges.collect { case Edge.Assumes(n, p) if
        Walk.breadthFirst(List(p), identity)(x => r.parents(x) ++ r.assumed(x)).contains(n) =>
      Problem.PremiseBelow(n, p) }

  /** What a node assumes is an assumption (2.4); what values from outside meet is assumed, and never a part. */
  private def premises(t: Theory): List[Problem] =
    t.edges.collect {
      case Edge.Assumes(n, p) if !t.node(p).exists(_.statement.kind == NodeKind.Assumption) =>
        Problem.PremiseNotAssumed(n, p)
      case Edge.PartOf(p, w) if t.node(p).exists(Outsides.aboutOutside) => Problem.OutsideAsPart(p, w)
    }

  private def underDesign(t: Theory): List[Problem] =
    for
      n <- t.refinement.nodes
      p <- t.refinement.parents(n.id).flatMap(t.refinement.node)
      if p.statement.kind == NodeKind.Design && n.statement.kind != NodeKind.Design
    yield Problem.UnderDesign(n.id, p.id)

  /** Each name declared once, none a name the generated prover files bind themselves (nor a hypothesis's, nor, of
    * a node, one of the modules laid out beside the nodes' or no plain name), and no statement mentioning a value
    * with no prover type. The FrModel's namespace is its name, so it is declared there too: a FrModel named as a type
    * or a value (`Booking` beside `Booking`) is declared twice.
    */
  private def vocabulary(t: Theory): ValidatedNec[Problem, Unit] =
    val v = t.vocabulary
    val names = v.sorts.map(_.name.value) ++ v.types.map(_.typeName.value) ++ v.symbols.map(_.name.value) ++
      v.defines.map(_.name.value) :+ t.name.value
    val (nodes, symbols) = (t.nodes.map(_.node.id).toSet, v.symbols.map(_.name).toSet)
    val hypotheses = v.symbols.map(_.name.value).filter(LeanNames.hypothesisLike(_, nodes, symbols))
    val modules = t.nodes.map(_.node.id.value).filter(n => LeanNames.Modules(n) || LeanNames.Keywords(n) ||
      !LeanNames.plain(n))
    all((names.filter(Reserved.names) ++ hypotheses ++ modules).distinct.map(Problem.ReservedName(_)) ++
      names.diff(names.distinct).distinct.map(Problem.DeclaredTwice(_)) ++
      t.nodes.map(_.node.id).flatMap(id => Constrained.of(t, id).flatMap(s =>
        Constrained.codeOnlyType(t, s).map(Problem.CodeOnlyInStatement(id, s, _)))) ++ Bounded.problems(t))

  /** A statement's `.assuming` lists exactly the facts about the outside its check rests on (`Premises`: derived,
    * and only checked), and every `always[T]` reaches each `T` covered code can make (`Unreached`).
    */
  private def outside(t: Theory): ValidatedNec[Problem, Unit] =
    val missing = t.nodes.map(_.node.id).flatMap(id => Premises.of(t, id)
      .filter(Outsides.assumed(t, id, _).isEmpty).map(p => Problem.PremiseMissing(id, p, Outsides.saying(t, p))))
    val unneeded = t.nodes.map(_.node.id).flatMap(id => Outsides.premises(t, id).filter(p =>
      t.node(p).exists(n => Outsides.aboutOutside(n) && !Premises.of(t, id).exists(Outsides.saysOf(n, _))))
      .map(Problem.PremiseNotNeeded(id, _)))
    all(missing ++ unneeded ++ Unreached.of(t))

  /** Code is for a Definition some statement mentions (a provided one with no prover type is read by plain code
    * only). Any part of a node checked against proven code is one `impl` may rest on: it takes every stated part as
    * a hypothesis, the code put in it (sound: the graph is acyclic and each part is checked against the same code).
    */
  private def code(t: Theory): ValidatedNec[Problem, Unit] =
    val unclaimed = t.code.attached.toList.collect {
      case (s, a) if !providedToCode(t, s, a.code) && Constrained.statements(t, s).isEmpty => s
    }
    all(unclaimed.map(Problem.CodeWithoutClaim(_)) ++ Resolve.circles(t).map(Problem.RestsOnItself(_)))

  /** A value with no prover type provided where the code runs (a connection), or a structure's member given a class. */
  private def providedToCode(t: Theory, s: SymbolName, c: Code): Boolean =
    t.code.unclaimed(s) || (Constrained.isCodeOnly(t, s) && c == Code.Provided)
