package frflow.core.analysis

import cats.syntax.all.*
import frflow.core.{Failing, Theory}
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Mentions}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.spec.{Statement, Written}
import frflow.core.term.{Annotation, Bound, Program, Sym, World}
import frflow.core.term.interpret.{Collect, Forward}
import frflow.core.ty.Ty
import frflow.core.vocab.{SymbolType, ValueKind}
import frflow.core.analysis.outside.Premises

/** `t.isConstant` as the FrModel states it (owner §44, §45 A): no run of any program from the world the statement
  * holds in changes `t`, whatever the run's outcome. One equation per program that changes what `t` reads, over its
  * inputs: `∀ x…, match p x… world with | (result, after) => t after = t world` (and, of a program that may fail,
  * the same of its failing runs). A program changes what `t` reads when its proven code writes a model `t` reads,
  * through the defines it calls (`Premises.writers`); one with no proven code may change anything, and so may every
  * program where `t` reads a Declaration that changes with the World (no code gives it a value: of it, `isConstant`
  * is an assumption). The world's own steps count as programs (the clock's `elapse`, owner §47: time passing must
  * keep it too). A new such program adds its equation, so the statement's meaning changes and it comes back to
  * review. The models `t` reads are noted (`Of`): what the reading rests on outside the code (`onlyCodeChanges`, a
  * run one step: `atomic`).
  */
object Constancy:
  /** The models an `isConstant` reads, noted on the equations stating it. */
  final case class Of(models: List[ModelName]) extends Annotation

  /** A program's run as an equation states it: its inputs, what it gives, the error it may fail with. */
  private final case class Run(op: SymbolName, ty: Ty, inputs: List[Ty], result: Ty, error: Option[Ty])

  def expanded(t: Theory): Theory =
    t.copy(nodes = t.nodes.map(s => s.copy(node = s.node.copy(statement = stated(t, s.node.statement)))))

  /** The models the `isConstant`s of a formula read. */
  def models(formula: Written[Expr]): List[ModelName] =
    Collect.of(formula.term).collect { case Of(ms) => ms }.flatten.distinct

  private def stated(t: Theory, s: Statement): Statement = s match
    case Statement.Claim(f, r) if written(f.value)   => Statement.Claim(expand(t, f), r)
    case Statement.Assumption(f) if written(f.value) => Statement.Assumption(expand(t, f))
    case other                                       => other

  private def written(e: Expr): Boolean = Exprs.all(e).exists {
    case Expr.Constant(_, _, _) => true
    case _                      => false
  }

  private def expand(t: Theory, f: Written[Expr]): Written[Expr] =
    val values = Exprs.all(f.value).collect { case Expr.Constant(_, _, v) => v }
    val read = values.foldMap(v => reads(t, v))
    val runs = programs(t, read)
    Written.formula([T[_]] => (s: Sym[T]) => f.term[T](Stated(s, runs, read.models)), f.source)

  /** What a value mentions, through the defines it calls. */
  private def reads(t: Theory, v: Expr): Mentions =
    val own = Exprs.mentions(v)
    own |+| t.vocabulary.closure(own.defines).foldMap(d => Exprs.mentions(d.lambda.body))

  /** The programs that may change what `read` mentions: every one, where it reads a Declaration of the World. */
  private def programs(t: Theory, read: Mentions): List[Run] =
    val worldly = read.symbols.flatMap(t.vocabulary.symbol).exists(s => s.kind == ValueKind.Declaration &&
      (s.ty match
        case SymbolType.Typed(Ty.FnOf(ins, _)) => ins.lastOption.contains(Ty.World)
        case _                                 => false))
    val writers = read.models.flatMap(t.vocabulary.model).flatMap(Premises.writers(t, _)).toSet
    val outside = t.vocabulary.models.flatMap(_.outside).toSet
    t.vocabulary.symbols.flatMap(s => (s.ty, s.kind) match
      case (SymbolType.Typed(ty), ValueKind.Definition) if outside(s.name) =>
        run(t, s.name, ty).filter(_ => worldly || writers(s.name))
      case (SymbolType.Typed(ty), ValueKind.Definition) if t.vocabulary.modelOf(s.name).isEmpty =>
        run(t, s.name, ty).filter(_ => worldly || writers(s.name) || !proven(t, s.name))
      case _                                                                                  => None)

  private def run(t: Theory, op: SymbolName, ty: Ty): Option[Run] =
    val error = Failing.escapingOf(t, op).headOption
    ty match
      case Ty.FnOf(ins, Ty.FlowOf(r, _)) => Some(Run(op, ty, ins, r, error))
      case Ty.FlowOf(r, _)               => Some(Run(op, ty, Nil, r, error))
      case _                             => None

  private def proven(t: Theory, op: SymbolName): Boolean = t.code.attached.get(op).exists(_.code match
    case Code.ProvenFlow(_) => true
    case _                  => false)

  /** Each `constant` as its equations, noted with the models its value reads. */
  private final class Stated[T[_]](protected val base: Sym[T], runs: List[Run], models: List[ModelName])
      extends Forward[T, T]:
    protected def fwd[A](t: T[A]): T[A] = t
    protected def bwd[A](u: T[A]): T[A] = u

    override def constant[A](before: T[World], at: Bound[World])(value: T[World] => T[A]): T[Boolean] =
      base.noted(Of(models), runs.map(kept(_, before, value)).reduceOption(base.and).getOrElse(base.bool(true)))

    /** `∀ x…`, the run of `r` on them from `before` leaving `value` as it was, on each of its outcomes. */
    private def kept[A](r: Run, before: T[World], value: T[World] => T[A]): T[Boolean] =
      def same(after: T[World]) = base.eq(value(after), value(before))
      def over(left: List[(Ty, Int)], args: List[T[Any]]): T[Boolean] = left match
        case (ty, i) :: rest => base.forall(Bound[Any](s"x$i", ty))(x => over(rest, args :+ x))
        case Nil             =>
          val p = args.foldLeft(base.param[Any](r.op, r.ty))((f, a) => base.app[Any, Any](f.asInstanceOf[T[Any => Any]],
            a)).asInstanceOf[T[Program[Any]]] // `r.op` applied to all its inputs: a program
          val after = Bound[World]("after", Ty.World)
          val ok = base.runs[Any](p, before, Bound[Any]("result", r.result), after)((_, a) => same(a))
          r.error.fold(ok)(e => base.and(ok, base.fails[Any, Any](p, before, Bound[Any]("error", e), after)((_, a) =>
            same(a))))
      over(r.inputs.zipWithIndex, Nil)
