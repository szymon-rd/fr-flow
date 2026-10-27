package frflow.proof.terms

import frflow.core.expr.{Binder, Expr, Exprs, Prog, Progs}
import frflow.core.name.VarId
import frflow.core.spec.Form
import frflow.core.term.{Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, Vocabulary}

/** A parallel step of a proven program (`parTupled`, `parTraverse`) read in its two orders, which `commute_i` states
  * give the same result and leave the same world from every world: the program's inputs and the steps before it that
  * it reads (`inputs`), for a traverse two of its elements apart, and the error the program may fail with. Whole
  * branches: what each order does step by step is not compared.
  */
final case class Commutation(inputs: List[Binder], apart: Option[Apart], first: Prog[Stated[?]],
    second: Prog[Stated[?]], result: Ty, error: Option[Ty])

object Commutation:
  /** Each parallel step of a program's define, in order. */
  def of(v: Vocabulary, d: Define): List[Commutation] = (d.written.form, d.lambda.body) match
    case (Form.Steps(p), Expr.Do(ir, _)) =>
      val error = (Progs.errors(ir) ++ Progs.boundaries(ir).flatMap(v.boundary).flatMap(_.failsWith)).headOption
      val fresh = (-ids(ir).minOption.getOrElse(0L)).max(0L).toInt
      Progs.parallel(p).zip(Progs.parallel(ir)).flatMap((step, read) =>
        orders(v, step, read, fresh).map((apart, first, second, result) =>
          Commutation(d.lambda.params ++ before(read), apart, first, second, result, error)))
    case _ => Nil

  private type Orders = (Option[Apart], Prog[Stated[?]], Prog[Stated[?]], Ty)

  private def orders(v: Vocabulary, step: Prog[Stated[?]], read: Prog[Expr], fresh: Int): Option[Orders] =
    (step, read) match
      case (Prog.Par(l, a, r, b), _) =>
        val both = pair(a, b)
        Some((None, Prog.Bind(l, a, Prog.Bind(r, b, both)), Prog.Bind(r, b, Prog.Bind(l, a, both)),
          Ty.TupleOf(List(a.ty, b.ty))))
      case (Prog.ParEach(xs, x, body, _), Prog.ParEach(_, _, readBody, _)) =>
        val ty = resultOf(v, readBody)
        def at(y: Binder) = Prog.Let(x, Stated([T[_]] => (s: Sym[T]) => s.free[Any](y)), body)
        val (one, two) = (Binder(VarId.step(fresh), s"${x.hint}_one", x.ty),
          Binder(VarId.step(fresh + 1), s"${x.hint}_two", x.ty))
        val (r1, r2) = (Binder(VarId.step(fresh + 2), "one", ty), Binder(VarId.step(fresh + 3), "two", ty))
        val both = pair(r1, r2)
        Some((Some(Apart(one, two, xs)), Prog.Bind(at(one), r1, Prog.Bind(at(two), r2, both)),
          Prog.Bind(at(two), r2, Prog.Bind(at(one), r1, both)), Ty.TupleOf(List(ty, ty))))
      case _ => None

  private def pair(a: Binder, b: Binder): Prog[Stated[?]] =
    Prog.Pure(Stated([T[_]] => (s: Sym[T]) => s.pair(s.free[Any](a), s.free[Any](b))))

  /** The steps bound before the parallel step that it reads: variables of its terms bound outside it. */
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

  /** The type of what the steps give. */
  private def resultOf(v: Vocabulary, p: Prog[Expr]): Ty = p match
    case Prog.Pure(e)                   => Exprs.typeOf(e)
    case Prog.Call(_, _, _, t)          => t
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
    case Prog.Loop(_, _, _) | Prog.Write(_, _) | Prog.Modify(_, _, _) => Ty.Unit
