package frflow.core.analysis

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.{Elaborated, Failing, Theory}
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, PrimOp, Prog, Progs}
import frflow.core.graph.{Edge, Walk}
import frflow.core.name.{LeanNames, NodeId, SymbolName}
import frflow.core.spec.NodeKind
import frflow.core.ty.Ty
import frflow.core.vocab.DefineForm
import frflow.core.analysis.outside.{Outsides, Premises}

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

  /** What a node assumes is an assumption (2.4); a fact about the outside, or what values from outside meet, is
    * assumed, and never a part.
    */
  private def premises(t: Theory): List[Problem] =
    t.edges.collect {
      case Edge.Assumes(n, p) if !t.node(p).exists(_.statement.kind == NodeKind.Assumption) =>
        Problem.PremiseNotAssumed(n, p)
      case Edge.PartOf(p, w) if t.node(p).exists(Outsides.aboutOutside) => Problem.OutsideAsPart(p, w)
    } ++ t.nodes.map(_.node).collect {
      case n if n.statement.kind == NodeKind.Claim && n.statement.outside.nonEmpty => Problem.OutsideClaimed(n.id)
    }

  private def underDesign(t: Theory): List[Problem] =
    for
      n <- t.refinement.nodes
      p <- t.refinement.parents(n.id).flatMap(t.refinement.node)
      if p.statement.kind == NodeKind.Design && n.statement.kind != NodeKind.Design
    yield Problem.UnderDesign(n.id, p.id)

  /** Each name declared once, none a name generated Lean binds itself (nor a hypothesis's, nor, of a node, one of
    * the modules laid out beside the nodes' or no plain Lean name), and no statement mentioning a value with no Lean
    * type. A model's namespace in Lean is its name capitalized (`Shelf`), and the FrModel's is its name, so
    * each is declared there too: a model named as a domain type (`shelf` beside `Shelf`), or a FrModel named as a
    * type or a value (`Booking` beside `Booking`), is declared twice.
    */
  private def vocabulary(t: Theory): ValidatedNec[Problem, Unit] =
    val v = t.vocabulary
    val names = v.sorts.map(_.name.value) ++ v.types.map(_.typeName.value) ++ v.symbols.map(_.name.value) ++
      v.defines.map(_.name.value) ++ v.models.map(_.name.value.capitalize) :+ t.name.value
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
    all(missing ++ unneeded ++ worldsEqual(t) ++ Unreached.of(t))

  /** An equation of worlds in a statement, where the worlds hold faults (a model's operations may fail). */
  private def worldsEqual(t: Theory): List[Problem] =
    if !t.vocabulary.models.exists(_.fails.nonEmpty) then Nil
    else t.nodes.map(_.node).filter(n => n.statement.exprs.flatMap(Exprs.all).exists {
      case Expr.Prim(PrimOp.Eq, a :: _, _) => Exprs.typeOf(a) == Ty.World
      case _                               => false
    }).map(n => Problem.WorldsEqual(n.id))

  /** Code is for a Definition some statement mentions (a provided one with no Lean type is read by plain code only;
    * an operation on a state is checked against its model).
    * A program fails with one error type, and a failing run's clause is of that type, on a program that can fail
    * (`Failing`). Any part of a node checked against proven code is one `impl` may rest on: it takes every stated part
    * as a hypothesis, the code put in it (sound: the graph is acyclic and each part is checked against the same code).
    */
  private def code(t: Theory): ValidatedNec[Problem, Unit] =
    val unclaimed = t.code.attached.toList.collect {
      case (s, a) if !providedToCode(t, s, a.code) && !modelled(a.code) && Constrained.statements(t, s).isEmpty => s
    }
    val differing = t.vocabulary.defines.collect {
      case d if d.form == DefineForm.Flow && Failing.of(t.vocabulary, d).size > 1 =>
        Problem.ErrorsDiffer(d.name, Failing.of(t.vocabulary, d))
    }
    val clauses = t.nodes.map(_.node).flatMap(n => n.statement.said.toList.flatMap(f => Failing.clauses(f.value))
      .flatMap((op, ty) => failingClause(t, n.id, op, ty)))
    val runs = t.nodes.map(_.node).filter(_.statement.said.exists(f => Failing.runsNoDefinition(f.value)))
      .map(n => Problem.RunOfNoDefinition(n.id))
    val nested = t.vocabulary.defines.filter(d => d.form == DefineForm.Flow && (d.lambda.body match
      case Expr.Do(p, _) => Progs.nestsAtomic(p)
      case _             => false)).map(d => Problem.NestedAtomic(d.name))
    all(unclaimed.map(Problem.CodeWithoutClaim(_)) ++ Resolve.circles(t).map(Problem.RestsOnItself(_)) ++ runs ++
      differing ++ clauses ++ nested ++ steps(t))

  /** A program's step calling a Definition that is no model's operation (another program, or one given plain Scala):
    * what it is handed would reach code no `made_` at the call covers, so it waits for its form (step 12).
    */
  private def steps(t: Theory): List[Problem] = t.vocabulary.defines.filter(_.form == DefineForm.Flow).flatMap(d =>
    d.lambda.body match
      case Expr.Do(p, _) => Progs.all(p).collect {
          case Prog.Call(op, _, _) if op != Prog.leftWins && t.vocabulary.modelOf(op).isEmpty =>
            Problem.StepNotOperation(d.name, op)
        }.distinct
      case _             => Nil)

  /** A failing run's clause on a program that cannot fail, or of another type than it fails with. */
  private def failingClause(t: Theory, id: NodeId, op: SymbolName, clause: Ty): Option[Problem] =
    Failing.escapingOf(t, op) match
      case Nil                               => Some(Problem.NeverFails(id, op))
      case errors if errors.contains(clause) => None
      case error :: _                        => Some(Problem.FailingDiffers(id, op, clause, error))

  private def modelled(c: Code): Boolean = c match
    case Code.Modelled(_) => true
    case _                => false

  /** A value with no Lean type, provided where the code runs (a connection): no statement can mention it. */
  private def providedToCode(t: Theory, s: SymbolName, c: Code): Boolean =
    Constrained.isCodeOnly(t, s) && c == Code.Provided
