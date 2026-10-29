package frflow.dsl.flow

import cats.data.State
import cats.kernel.Monoid
import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Prog, Side, Value}
import frflow.core.name.VarId
import frflow.core.term.{Stated, Sym}
import frflow.core.ty.Ty
import frflow.dsl.build.{Failure, Fault}
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.dsl.vocab.Called

/** A recorded program read into the `Prog` Lean proves and production runs, its terms kept as terms (`Stated`), with
  * the notes of every term it met. Each step's result is bound to a variable this reading numbers (`VarId.step`, a
  * counter in its own `State`, not ambient); a step's reading wraps the steps after it, and gives its result as the
  * next step receives it: the unit, or a term.
  */
object ReadRecording:
  private type P = Prog[Stated[?]]

  def apply[R](r: Recorded[Term[R]]): (P, Notes) = steps(r)

  /** The steps of anything recorded, its result a term or the unit (a model's operation that returns nothing). */
  def steps[A](r: Recorded[A]): (P, Notes) =
    val (seen, prog) = Reader.whole(r).map(_._1).run(Seen(0, Monoid[Notes].empty)).value
    (prog, seen.notes)

  /** What the reading has seen: the next step's number, and the notes of the terms met so far. */
  private final case class Seen(next: Int, notes: Notes)
  private type Reading = State[Seen, (P => P, Any)]

  private object Reader:
    def read[A](r: Recorded[A]): Reading = r match
      case Recorded.Pure(a)               => noted(a).as((identity, a))
      case Recorded.Call(applied, t)      => noted(applied) *> called(applied, t)
      case b: Recorded.Bind[x, A]         => bind(b)
      case Recorded.Cond(c, t, e)         => noted(c) *> cond(c, t(), e())
      case Recorded.Each(xs, t, body)     => noted(xs) *> each(xs, t, body)
      case Recorded.Collect(xs, t, b, ty) => noted(xs) *> collected(xs, t, b, ty)(Prog.Collect(_, _, _))
      case Recorded.ParCollect(xs, t, b, ty, n) => noted(xs) *> collected(xs, t, b, ty)(Prog.ParEach(_, _, _, n))
      case Recorded.Fold(xs, z, t, body)  => noted(xs) *> noted(z) *> fold(xs, z, t, body)
      case Recorded.Raise(e)              => noted(e) *> raised(e)
      case Recorded.Handle(body, e, h)    => handle(body, e, h)
      case Recorded.Atomic(body)          => whole(body).flatMap((p, ty) => bound(Prog.Atomic(p), ty))
      case Recorded.Read(m, t)            => bound(Prog.Read(m), t)
      case Recorded.Write(m, s)           => noted(s) *> bound(Prog.Write(m, expr(s)), LeanType[Unit])
      case Recorded.Par(l, r, t)          => par(l, r, t)
      case Recorded.Race(l, r, t)         => race(l, r, t)
      case Recorded.Guard(body, err, fin) => guard(body, err.ty, fin)

    /** An operation's call: the Definition the term applies, and its arguments. */
    private def called(applied: Term[?], t: LeanType[?]): Reading = Called.of(applied).fold(
      throw Failure(Fault.NotAnOperation(applied.expr.getClass.getSimpleName)))((op, as) =>
      bound(Prog.Call(op, as.map(expr), t.ty), t))

    /** A raise: the steps after it never run, so they are dropped; the next step is given a variable of no value
      * (`Ty.Never`), whatever it expects, so a program raising and then mapping is read.
      */
    private def raised(e: Term[?]): Reading =
      fresh(Ty.Never).map(x => (_ => Prog.Raise(expr(e)), Term.free(x)(using LeanType.of[Nothing](Ty.Never))))

    /** A whole sub-program: its steps ending in its result, and the result's type. */
    def whole[A](r: Recorded[A]): State[Seen, (P, LeanType[?])] =
      read(r).map((wrap, result) => (wrap(Prog.Pure(exprOf(result))), typeOf(result)))

    /** A term computed and bound is shared (a `let`); any other result is given to the next step as it is. */
    private def bind[X, A](b: Recorded.Bind[X, A]): Reading = b.first match
      case Recorded.Pure(t: Term[?]) if computed(t.expr) => noted(t) *> shared(t, b.next)
      case first                                          =>
        for (w1, a) <- read(first); (w2, out) <- read(b.next(a.asInstanceOf[X])) yield (w1 compose w2, out)

    private def shared[X](t: Term[?], next: X => Recorded[?]): Reading =
      for x <- fresh(t.leanType.ty); (w, out) <- read(next(valueOf[X](x, t.leanType)))
      yield (rest => Prog.Let(x, expr(t), w(rest)), out)

    private def computed(e: Expr): Boolean = e match
      case Expr.Var(_) | Expr.Lit(_, _) => false
      case _                            => true

    private def cond[A](c: Term[Boolean], ifTrue: Recorded[A], ifFalse: Recorded[A]): Reading =
      for (pt, t) <- whole(ifTrue); (pe, _) <- whole(ifFalse); out <- bound(Prog.Branch(expr(c), pt, pe), t)
      yield out

    /** The body once per element, the element bound to a fresh variable of the list's element type. */
    private def each[X](xs: Term[List[X]], t: LeanType[X], body: Term[X] => Recorded[Unit]): Reading =
      for x <- fresh(t.ty); (pb, _) <- whole(body(Term.free(x)(using t)))
          out <- bound(Prog.Loop(expr(xs), x, pb), LeanType[Unit])
      yield out

    /** The body once per element, its results collected: one element after another, or all at once. */
    private def collected[X](xs: Term[List[X]], t: LeanType[X], body: Term[X] => Recorded[?], ty: LeanType[?])(
        step: (Stated[?], Binder, P) => P): Reading =
      for x <- fresh(t.ty); (pb, _) <- whole(body(Term.free(x)(using t))); out <- bound(step(expr(xs), x, pb), ty)
      yield out

    /** The body once per element, on the value carried so far and the element, each bound to a fresh variable. */
    private def fold[X, B](xs: Term[List[X]], z: Term[B], t: LeanType[X], body: (Term[B], Term[X]) => Recorded[?])
        : Reading =
      for acc <- fresh(z.leanType.ty); x <- fresh(t.ty)
          (pb, _) <- whole(body(Term.free(acc)(using z.leanType), Term.free(x)(using t)))
          out <- bound(Prog.Accumulate(expr(xs), expr(z), acc, x, pb), z.leanType)
      yield out

    /** The body, and the handler on an error of type `err` it raises, bound to a fresh variable. */
    private def handle[E, A](body: Recorded[A], err: LeanType[E], handler: Term[E] => Recorded[A]): Reading =
      for (pb, t) <- whole(body); e <- fresh(err.ty); (ph, _) <- whole(handler(Term.free(e)(using err)))
          out <- bound(Prog.Catch(pb, err.ty, e, ph), t)
      yield out

    private def par[L, R](l: Recorded[L], r: Recorded[R], t: LeanType[?]): Reading =
      for (pl, tl) <- whole(l); (pr, tr) <- whole(r); a <- fresh(tl.ty); b <- fresh(tr.ty)
          out <- bound(Prog.Par(pl, a, pr, b), t)
      yield out

    private def race[L, R](l: Recorded[L], r: Recorded[R], t: LeanType[?]): Reading =
      for (pl, _) <- whole(l); (pr, _) <- whole(r); reading <- raced(pl, pr, t.ty)
          out <- bound(Prog.Race(pl, pr, reading), t)
      yield out

    private def guard[A](body: Recorded[A], err: Ty, fin: Recorded[Unit]): Reading =
      for (pb, t) <- whole(body); (pf, _) <- whole(fin); reading <- guarded(pb, t.ty, err, pf)
          out <- bound(Prog.Guard(pb, err, pf, reading), t)
      yield out

    /** A step whose result is bound to a fresh variable, which the next step receives. */
    private def bound(step: P, t: LeanType[?]): Reading =
      fresh(t.ty).map(x => (rest => Prog.Bind(step, x, rest), valueOf[Any](x, t)))

    private def expr(t: Term[?]): Stated[?] = Stated(t.run)

    private def typeOf(a: Any): LeanType[?] = a match
      case t: Term[?] => t.leanType
      case _          => LeanType[Unit]

    private def exprOf(a: Any): Stated[?] = a match
      case t: Term[?] => expr(t)
      case ()         => unit
      case other      => throw Failure(Fault.NotATerm(other.getClass.getSimpleName))

  /** The scheduler's choice of the winner (`Prog.leftWins`), then the winner's steps. */
  private def raced(left: P, right: P, ty: Ty): State[Seen, P] = fresh(Ty.Bool).map(w =>
    Prog.Bind(Prog.Call(Prog.leftWins, Nil, Ty.Bool), w,
      Prog.Branch(variable(w), injected(left, Side.Error, ty), injected(right, Side.Value, ty))))

  /** The finalizer after a result, and before an error of type `err` is raised again. */
  private def guarded(body: P, ty: Ty, err: Ty, fin: P): State[Seen, P] =
    for x <- fresh(ty); e <- fresh(err); u <- fresh(Ty.Unit); v <- fresh(Ty.Unit)
    yield Prog.Bind(Prog.Catch(body, err, e, Prog.Bind(fin, u, Prog.Raise(variable(e)))), x,
      Prog.Bind(fin, v, Prog.Pure(variable(x))))

  private def injected(p: P, side: Side, ty: Ty): P = p match
    case Prog.Pure(e)          => Prog.Pure(inject(e, side, ty))
    case Prog.Bind(s, x, rest) => Prog.Bind(s, x, injected(rest, side, ty))
    case Prog.Let(x, v, rest)  => Prog.Let(x, v, injected(rest, side, ty))
    case other                 => other // a sub-program's steps end in `Pure` (`whole`), or raise

  /** A step's result as the next step receives it: the unit, or the variable bound to it as a term of its type. The
    * recording hands each step's result to the program's next function (`Recorded.Bind`), which forgot its type:
    * the one cast of the reading, of a value made here of the type the step was recorded with.
    */
  private def valueOf[X](x: Binder, t: LeanType[?]): X =
    (if x.ty == Ty.Unit then () else Term.free(x)(using t)).asInstanceOf[X]

  private def fresh(ty: Ty): State[Seen, Binder] =
    State(s => (s.copy(next = s.next + 1), Binder(VarId.step(s.next), if ty == Ty.Unit then "_$u" else "r", ty)))

  private def noted(a: Any): State[Seen, Unit] = a match
    case t: Term[?] => State.modify(s => s.copy(notes = s.notes |+| t.notes))
    case _          => State.pure(())

  /** A sub-program's result as the side of an `Either` it is (a race's winner). */
  private def inject[A](e: Stated[A], side: Side, ty: Ty): Stated[?] =
    if side == Side.Error then Stated([T[_]] => (s: Sym[T]) => s.left[A, Any](e.run(s), ty))
    else Stated([T[_]] => (s: Sym[T]) => s.right[Any, A](e.run(s), ty))

  private def variable(x: Binder): Stated[?] = Stated([T[_]] => (s: Sym[T]) => s.free[Any](x))
  private val unit: Stated[?] = Stated([T[_]] => (s: Sym[T]) => s.lit((), Value.Unit, Ty.Unit))
