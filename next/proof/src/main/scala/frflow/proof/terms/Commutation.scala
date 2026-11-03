package frflow.proof.terms

import cats.syntax.all.*
import frflow.core.analysis.AtOnce
import frflow.core.expr.{Binder, Expr, Exprs, Prog, Progs}
import frflow.core.name.VarId
import frflow.core.spec.Form
import frflow.core.term.{Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, Vocabulary}

/** Two steps of a proven program at once, one of each side of a concurrent step (`AtOnce.pairs`: a pair's branches,
  * two elements of a traverse at once, a race's sides) and touching a model in common, read in their two orders,
  * which `commute_i` states give the same results and leave the same models from every world. Over the program's
  * inputs and the steps before the concurrent step that it reads, and every value of each side's own variables the
  * steps read (`inputs`; each side its own, `x_one` and `x_two`), for a traverse two of its elements (`apart`); with
  * the error the program may fail with, each step's outcome its own (`FrFlow.caught`): a step's failure ends its
  * side, not the other's.
  */
final case class Commutation(inputs: List[Binder], apart: Option[Apart], first: Prog[Stated[?]],
    second: Prog[Stated[?]], result: Ty, error: Option[Ty])

object Commutation:
  private type P = Prog[Stated[?]]

  /** Each pair of steps at once of a program's define, numbered across its concurrent steps. */
  def of(v: Vocabulary, d: Define): List[Commutation] = (d.written.form, d.lambda.body) match
    case (Form.Steps(p), Expr.Do(ir, _)) =>
      val fresh = (-ids(ir).minOption.getOrElse(0L)).max(0L).toInt
      val (written, read) = (AtOnce.of(p), AtOnce.of(ir))
      AtOnce.all(v, ir).flatMap((n, ij) =>
        (AtOnce.sides(written(n)), AtOnce.sides(read(n))).tupled.map((ws, rs) =>
          Pairing(v, d, written(n), read(n), fresh)(ws, rs, ij)))
    case _ => Nil

  /** One pair's commutation, its fresh variables numbered from `fresh`. */
  private final case class Pairing(v: Vocabulary, d: Define, written: P, read: Prog[Expr], fresh: Int):
    private val shared = before(read).map(_.id).toSet

    def apply(ws: (P, P), rs: (Prog[Expr], Prog[Expr]), ij: (Int, Int)): Commutation =
      val (s, t) = (AtOnce.units(ws._1)(ij._1), AtOnce.units(ws._2)(ij._2))
      val (si, ti) = (AtOnce.units(rs._1)(ij._1), AtOnce.units(rs._2)(ij._2))
      val ownS = own(si, 2, "one", apart.map((x, a) => x -> a.one))
      val ownT = own(ti, 2 + ownS.size, "two", apart.map((x, a) => x -> a.two))
      val k = 2 + ownS.size + ownT.size
      val (a, b) = (at(k, "one", resultOf(v, si)), at(k + 1, "two", resultOf(v, ti)))
      val (s1, t1, both) = (wrapped(s, ownS), wrapped(t, ownT), pair(a, b))
      val elements = apart.toList.flatMap((_, a) => List(a.one, a.two)).map(_.id).toSet
      Commutation(d.lambda.params ++ before(read) ++ (ownS ++ ownT).map(_._2).filterNot(x => elements(x.id)),
        apart.map(_._2), Prog.Bind(s1, a, Prog.Bind(t1, b, both)), Prog.Bind(t1, b, Prog.Bind(s1, a, both)),
        Ty.TupleOf(List(a.ty, b.ty)), Ty.errorOf(d.lambda.result))

    /** A traverse's element, and the two elements the pair's steps are at. */
    private val apart: Option[(Binder, Apart)] = written match
      case Prog.ParEach(xs, x, _, _) =>
        Some(x -> Apart(at(0, s"${x.hint}_one", x.ty), at(1, s"${x.hint}_two", x.ty), xs))
      case _                         => None

    private def at(k: Int, hint: String, ty: Ty) = Binder(VarId.step(fresh + k), hint, ty)

    /** A step's own variables (bound in its side, outside it), each given a fresh one: the element's, if a
      * traverse's.
      */
    private def own(step: Prog[Expr], from: Int, side: String, element: Option[(Binder, Binder)])
        : List[(Binder, Binder)] =
      before(step).filterNot(x => shared(x.id)).zipWithIndex.map((x, k) =>
        x -> element.collect { case (e, y) if e.id == x.id => y }.getOrElse(at(from + k, s"${x.hint}_$side", x.ty)))

  /** The step with each of its own variables bound to its fresh one. */
  private def wrapped(step: P, own: List[(Binder, Binder)]): P =
    own.foldRight(step)((xy, body) => Prog.Let(xy._1, Stated([T[_]] => (s: Sym[T]) => s.free[Any](xy._2)), body))

  private def pair(a: Binder, b: Binder): P =
    Prog.Pure(Stated([T[_]] => (s: Sym[T]) => s.pair(s.free[Any](a), s.free[Any](b))))

  /** The steps bound outside `read` that it reads: variables of its terms bound outside it. */
  private def before(read: Prog[Expr]): List[Binder] =
    val inside = ids(read).toSet
    Progs.terms(read).flatMap(Exprs.all).collect { case Expr.Var(x) if x.id.value < 0 && !inside(x.id.value) => x }
      .distinct

  /** The ids of every variable the steps bind, in their structure and in their terms. */
  private def ids(p: Prog[Expr]): List[Long] =
    (Progs.all(p).flatMap(bound) ++ Progs.terms(p).flatMap(Exprs.all).flatMap(Exprs.binders)).map(_.id.value)

  private def bound(p: Prog[Expr]): List[Binder] = p match
    case Prog.Bind(_, x, _)             => List(x)
    case Prog.Let(x, _, _)              => List(x)
    case Prog.Loop(_, x, _)             => List(x)
    case Prog.Collect(_, x, _)          => List(x)
    case Prog.Accumulate(_, _, a, x, _) => List(a, x)
    case Prog.Modify(_, x, _)           => List(x)
    case Prog.Catch(_, _, x, _)         => List(x)
    case Prog.Par(_, a, _, b)           => List(a, b)
    case Prog.ParEach(_, x, _, _)       => List(x)
    case _                              => Nil

  /** The type of what a step gives: an operation's call, a transaction's body. */
  private def resultOf(v: Vocabulary, p: Prog[Expr]): Ty = p match
    case Prog.Pure(e)                   => Exprs.typeOf(e)
    case Prog.Call(_, _, t)             => t
    case Prog.Bind(_, _, r)             => resultOf(v, r)
    case Prog.Let(_, _, r)              => resultOf(v, r)
    case Prog.Collect(_, _, b)          => Ty.ListOf(resultOf(v, b))
    case Prog.ParEach(_, _, b, _)       => Ty.ListOf(resultOf(v, b))
    case Prog.Accumulate(_, z, _, _, _) => Exprs.typeOf(z)
    case Prog.Branch(_, a, b)           => Ty.join(resultOf(v, a), resultOf(v, b))
    case Prog.Catch(b, _, _, h)         => Ty.join(resultOf(v, b), resultOf(v, h))
    case Prog.Read(m)                   => v.model(m).fold(Ty.Unit)(_.state)
    case Prog.Raise(_)                  => Ty.Never
    case Prog.Par(_, a, _, b)           => Ty.TupleOf(List(a.ty, b.ty))
    case Prog.Atomic(b)                 => resultOf(v, b)
    case Prog.Race(_, _, r)             => resultOf(v, r)
    case Prog.Guard(_, _, _, r)         => resultOf(v, r)
    case Prog.Loop(_, _, _) | Prog.Write(_, _) | Prog.Modify(_, _, _) | Prog.Cut(_) => Ty.Unit
