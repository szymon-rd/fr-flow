package frflow.core.analysis

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.{Elaborated, Theory}
import frflow.core.graph.Edge
import frflow.core.name.Words
import frflow.core.spec.{Node, NodeKind, Statement}
import frflow.core.vocab.SymbolType

/** The structure rules (docs/DAG.md §2) as one pure function: every problem at once, or the theory as `Valid`. */
object Validate:
  def apply(e: Elaborated): ValidatedNec[Problem, Valid] =
    val t = e.theory
    (structure(t), vocabulary(t), invariants(t), exemptions(t), givens(t), code(t))
      .mapN((_, _, _, _, _, _) => Valid(e))

  private def all(ps: List[Problem]): ValidatedNec[Problem, Unit] =
    NonEmptyChain.fromSeq(ps).fold(Validated.validNec(()))(Validated.invalid)

  private def structure(t: Theory): ValidatedNec[Problem, Unit] =
    val r = t.refinement
    val ids = t.nodes.map(_.node.id)
    val roots = r.roots.map(_.id) match
      case List(_)                    => Nil
      case Nil if t.nodes.isEmpty     => Nil // a new project
      case Nil                        => List(Problem.NoRoot)
      case several                    => List(Problem.SeveralRoots(several))
    all(ids.diff(ids.distinct).distinct.map(Problem.DuplicateId(_)) ++ roots ++
      r.nodes.filter(n => r.ancestors(n.id).contains(n.id)).map(n => Problem.AboveItself(n.id)) ++
      r.nodes.flatMap(n => r.parents(n.id).filterNot(ids.contains).map(Problem.ParentOutside(n.id, _))) ++
      r.nodes.collect { case n if n.statement.kind == NodeKind.Design && r.parents(n.id).isEmpty =>
        Problem.DesignWithoutParent(n.id) } ++
      underWrongKind(t))

  private def underWrongKind(t: Theory): List[Problem] =
    for
      n <- t.refinement.nodes
      p <- t.refinement.parents(n.id).flatMap(t.refinement.node)
      problem <- (p.statement, n.statement) match
        case (Statement.Design(_), Statement.Design(_)) => None
        case (Statement.Design(_), _)                   => Some(Problem.UnderDesign(n.id, p.id))
        case (Statement.Definition(_), _)               => Some(Problem.UnderDefinition(n.id, p.id))
        case _                                          => None
    yield problem

  /** Each name declared once; the definitions' rules (`definitions`). */
  private def vocabulary(t: Theory): ValidatedNec[Problem, Unit] =
    val v = t.vocabulary
    val names = v.sorts.map(_.name.value) ++ v.types.map(_.typeName.value) ++ v.symbols.map(_.name.value) ++
      v.defines.map(_.name.value)
    all(names.diff(names.distinct).distinct.map(Problem.DeclaredTwice(_))) *> definitions(t)

  private def definitions(t: Theory): ValidatedNec[Problem, Unit] = ???

  /** Every node in an invariant's scope keeps it or is exempt; some contract keeps it; its scope is in the graph. */
  private def invariants(t: Theory): ValidatedNec[Problem, Unit] =
    all(t.refinement.nodes.collect { case n @ Node(_, _, Statement.Invariant(_, scope)) => (n.id, scope) }.flatMap {
      (i, scope) =>
        Scope.of(t, i).filterNot(Scope.answers(t, i, _)).map(Problem.NotKeptInScope(i, _)) ++
          Option.unless(t.edges.exists { case Edge.Keeps(_, `i`, _) => true; case _ => false })(Problem.NoKeeper(i)) ++
          scope.filterNot(s => t.node(s).isDefined).map(Problem.ScopeOutside(i, _))
    })
  /** An invariant named once per node; exemptions only on contracts and designs, each with a reason. */
  private def exemptions(t: Theory): ValidatedNec[Problem, Unit] =
    val named = t.edges.collect { case Edge.Keeps(n, i, _) => (n, i); case Edge.Exempt(n, i, _) => (n, i) }
    all(named.diff(named.distinct).distinct.map(Problem.NamedTwice(_, _)) ++ t.edges.flatMap(exemption(t, _)))

  /** Every problem of one exemption: on a node that keeps no invariant, without a reason. */
  private def exemption(t: Theory, e: Edge): List[Problem] = e match
    case Edge.Exempt(n, i, why) =>
      Option.unless(t.node(n).exists(m => keeps(m.statement)))(Problem.ExemptWrongKind(n, i)).toList ++
        Option.unless(Words.enough(why))(Problem.ExemptWithoutReason(n, i))
    case _ => Nil

  private def keeps(s: Statement): Boolean = s match
    case Statement.Contract(_, _, _) | Statement.FlowContract(_, _, _, _) | Statement.Design(_) => true
    case _                                                                                    => false

  /** A code-only symbol (a connection) is given only as code: data for it has no type to be built as. */
  private def givens(t: Theory): ValidatedNec[Problem, Unit] =
    val codeOnly = t.vocabulary.symbols.filter(_.ty == SymbolType.CodeOnly).map(_.name).toSet
    all(t.nodes.map(_.node).flatMap(n => n.statement.givens.collect {
      case g if codeOnly(g.symbol) && g.supply.literal => Problem.DataForCodeOnly(n.id, g.symbol)
    }).distinct)

  private def code(t: Theory): ValidatedNec[Problem, Unit] = ???
