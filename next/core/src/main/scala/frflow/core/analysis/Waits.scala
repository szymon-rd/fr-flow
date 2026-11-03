package frflow.core.analysis

import cats.{Applicative, Id}
import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Prog, Progs}
import frflow.core.name.VarId
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.{Define, Timed, Vocabulary}

/** Waits at once, as Lean reads them (owner §47; the step 13 re-review's RN1). Read in turn, two waits at once would
  * add up, while a real run of them takes about the longer. So a wait inside a concurrent step is read as two points:
  * where the sides start (the time read once, before them: `start`, a lower bound of every wait's own start in
  * them) and its end, the clock reaching at least `start` plus its seconds (`Prog.reach`). Two such ends commute (the
  * later of the two), so the reading in turn of waits at once takes the longest, not the sum; a read of the clock
  * beside one does not commute, and is left to `commute_i` to refuse. A wait in turn stays one step, at least its
  * seconds. Lean's reading only: production and the Scala tests run the waits as written.
  */
object Waits:
  private val seconds = Ty.Num(NumKind.Big)

  /** `p` with each concurrent step holding a wait given its start, the new variables numbered from `from` on. */
  def read[E](p: Prog[E], clock: Timed, from: Int)(using vars: Prog.Vars[E]): Prog[E] =
    def outer(q: Prog[E]): State[Int, Prog[E]] = q match
      case Prog.Par(_, _, _, _) | Prog.ParEach(_, _, _, _) | Prog.Race(_, _, _) if waits(q, clock) =>
        State(n =>
          val start = Binder(VarId.step(n), "start", seconds)
          (n + 1, Prog.Bind(Prog.Call(clock.now, Nil, seconds), start,
            mapped[Id, E](q)(inside(_, clock, vars.variable(start))))))
      case other => mapped(other)(outer)
    outer(p).runA(from).value

  /** A program as Lean reads it: its waits at once each given its start, in its steps and their IR alike, the new
    * variables numbered past every one it binds. Any other define, or where the World has no clock, as it is.
    */
  def of(v: Vocabulary, d: Define): Define = (v.models.flatMap(_.timed).headOption, d.lambda.body) match
    case (Some(clock), Expr.Do(ir, _)) if AtOnce.of(ir).exists(waits(_, clock)) =>
      val from = (-Progs.binders(ir).map(_.id.value).minOption.getOrElse(0L)).max(0L).toInt
      d.copy(written = d.written.reread(read(_, clock, from), read(_, clock, from)))
    case _ => d

  /** Whether a concurrent step waits in one of its sides. */
  def waits[E](p: Prog[E], clock: Timed): Boolean = deep(p).exists {
    case Prog.Call(op, _, _) => op == clock.sleep
    case _                   => false
  }

  /** Every step inside `p`, a race's and a finalizer's sides as written and as read. */
  private def deep[E](p: Prog[E]): List[Prog[E]] = p :: (p match
    case Prog.Race(l, r, reading)       => List(l, r, reading).flatMap(deep)
    case Prog.Guard(b, _, f, reading)   => List(b, f, reading).flatMap(deep)
    case other                          => Progs.children(other).flatMap(deep))

  private def inside[E](p: Prog[E], clock: Timed, start: E): Prog[E] = p match
    case Prog.Call(op, List(d), ty) if op == clock.sleep => Prog.Call(Prog.reach, List(start, d), ty)
    case other                                          => mapped[Id, E](other)(inside(_, clock, start))

  /** `p` with `f` applied to each step directly inside it, a race's and a finalizer's sides included. */
  private def mapped[F[_]: Applicative, E](p: Prog[E])(f: Prog[E] => F[Prog[E]]): F[Prog[E]] = p match
    case Prog.Bind(a, x, r)              => (f(a), f(r)).mapN(Prog.Bind(_, x, _))
    case Prog.Let(x, v, r)               => f(r).map(Prog.Let(x, v, _))
    case Prog.Loop(xs, x, b)             => f(b).map(Prog.Loop(xs, x, _))
    case Prog.Collect(xs, x, b)          => f(b).map(Prog.Collect(xs, x, _))
    case Prog.Accumulate(xs, z, a, x, b) => f(b).map(Prog.Accumulate(xs, z, a, x, _))
    case Prog.Branch(c, a, b)            => (f(a), f(b)).mapN(Prog.Branch(c, _, _))
    case Prog.Catch(a, t, x, h)          => (f(a), f(h)).mapN(Prog.Catch(_, t, x, _))
    case Prog.Par(l, a, r, b)            => (f(l), f(r)).mapN(Prog.Par(_, a, _, b))
    case Prog.ParEach(xs, x, b, n)       => f(b).map(Prog.ParEach(xs, x, _, n))
    case Prog.Atomic(b)                  => f(b).map(Prog.Atomic(_))
    case Prog.Cut(b)                     => f(b).map(Prog.Cut(_))
    case Prog.Race(l, r, reading)        => (f(l), f(r), f(reading)).mapN(Prog.Race(_, _, _))
    case Prog.Guard(b, t, g, reading)    => (f(b), f(g), f(reading)).mapN(Prog.Guard(_, t, _, _))
    case leaf                            => leaf.pure[F]
