package frflow.dsl.kb

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.expr.{Expr, PrimOp}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Range, Statement}
import frflow.core.vocab.ValueKind
import frflow.dsl.build.{Declarations, ElabError, Fault, Site}
import frflow.dsl.node.Node
import frflow.dsl.run.Worlds
import frflow.dsl.vocab.Stating

/** Which Declarations change with the World (owner §43), read off the FrModel's statements: those a statement reads
  * beside what changes with it (a model's state, a program's run, a define reading state, `isConstant`, or another
  * such Declaration), until no statement adds one. Every Declaration may change with the World; one no statement
  * reads so is the same in each world whatever it is, so Lean is given it as a value, not a function of the world.
  * A rule (`always`) holds of values, in no world: a Declaration it reads is a value, which an assumption that it
  * never changes (`isConstant`) must say (`Fault.RuleOverChanging` otherwise). Each statement is read once open for
  * this (`Stating.probing`), then elaborated over the world it holds in.
  */
object Varying:
  /** What one statement read open tells: its Declarations, whether it reads the world, whether it is a rule, and
    * the Declarations it assumes never change.
    */
  private final case class Read(node: NodeId, declarations: Set[SymbolName], world: Boolean, rule: Boolean,
      fixed: Set[SymbolName])

  def of(nodes: List[Node]): ValidatedNec[ElabError, Set[SymbolName]] =
    val read = nodes.flatMap(n => n.statement(Stating.probing).run.toOption.flatMap((ds, s) =>
      s.said.map(f => Read(n.head.id, mentioned(ds), Worlds.in(f.value), s.range.exists(_ != Range.Possible),
        assumed(s, f.value)))))
    val values = read.filter(_.rule).flatMap(_.declarations).toSet
    val fixed = read.flatMap(_.fixed).toSet
    val missing = read.filter(_.rule).flatMap(r => (r.declarations -- fixed).toList.sortBy(_.value).map(d =>
      ElabError(Site.Node(r.node), Fault.RuleOverChanging(d.value, r.node.value))))
    val statements = read.filterNot(_.rule).map(_.declarations -- values)
    NonEmptyChain.fromSeq(missing).fold(Validated.validNec(closure(read.filter(r => r.world && !r.rule)
      .flatMap(_.declarations).toSet -- values, statements)))(Validated.invalid)

  /** Every Declaration a statement mentions beside one that changes, added until none is. */
  private def closure(varying: Set[SymbolName], statements: List[Set[SymbolName]]): Set[SymbolName] =
    val more = varying ++ statements.filter(_.exists(varying)).flatten
    if more == varying then varying else closure(more, statements)

  /** The Declarations a statement mentions, its rule's (a define it declares) among them. */
  private def mentioned(ds: Declarations): Set[SymbolName] =
    val rules = ds.defines.values.flatten.toList.flatMap(_.run.toOption.map(_._1))
    (ds :: rules).flatMap(_.symbols.collect { case (n, ss) if ss.exists(_.kind == ValueKind.Declaration) => n })
      .toSet

  /** The Declaration an assumption of `isConstant` is of: read open, `d … world = d … world` (`Declaration`). */
  private def assumed(s: Statement, e: Expr): Set[SymbolName] = s match
    case Statement.Assumption(_) => constant(e).toSet
    case _                       => Set.empty

  private def constant(e: Expr): Option[SymbolName] = e match
    case Expr.Quant(_, _, body)                                   => constant(body)
    case Expr.Prim(PrimOp.Eq, List(a @ Expr.Apply(Expr.Sym(d, _), args, _), b), _) if a == b && args.lastOption
        .contains(Expr.Var(Worlds.binder)) => Some(d)
    case _                                                        => None
