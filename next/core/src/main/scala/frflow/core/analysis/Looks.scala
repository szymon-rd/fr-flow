package frflow.core.analysis

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Prog, Progs}
import frflow.core.name.{DefName, SymbolName, VarId}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.{Define, Timed, Vocabulary}

/** A run's look at the clock after other steps, as Lean reads it (owner §47: the world may move the time at any step
  * of a run; the step 13d re-review's R-B2). Lean moves the time after each of the clock's steps (the tick), so what
  * passes between two looks is the tick after the first. Before a run's first look nothing has ticked: a look with
  * other steps before it is given a look first, its time dropped, the tick after it the time passing at those steps.
  * So only a run looking first reads the world's time. A call of a program that may look at the clock is given one
  * so too, its own looks then read from where it starts. Lean's reading only: production and the Scala tests run the
  * program as written.
  */
object Looks:
  private val seconds = Ty.Num(NumKind.Big)

  /** Where a run is: whether a step came before, and whether the clock stepped (and ticked) since on every path. */
  private final case class At(stepped: Boolean, looked: Boolean):
    def or(other: At): At = At(stepped || other.stepped, looked && other.looked)

  /** A program as Lean reads it: each late look given a look before it, the new variables numbered past every one it
    * binds. Any other define as it is.
    */
  def of(v: Vocabulary, clock: Timed, d: Define): Define = d.lambda.body match
    case Expr.Do(ir, _) =>
      val from = (-Progs.binders(ir).map(_.id.value).minOption.getOrElse(0L)).max(0L).toInt
      val reading = Reading(clock, looking(v, clock))
      d.copy(written = d.written.reread(reading.of(_, from), reading.of(_, from)))
    case _              => d

  /** Whether a call of `op` may look at the clock: one of the clock's steps, or a program calling one. */
  private def looking(v: Vocabulary, clock: Timed): SymbolName => Boolean =
    def go(seen: Set[SymbolName])(op: SymbolName): Boolean = op == clock.now || op == clock.sleep ||
      (!seen(op) && v.define(DefName(op.value)).exists(_.lambda.body match
        case Expr.Do(ir, _) => Progs.operations(ir).exists(go(seen + op))
        case _              => false))
    go(Set.empty)

  private final class Reading(clock: Timed, looking: SymbolName => Boolean):
    private type S[A] = State[Int, A]

    def of[E](p: Prog[E], from: Int): Prog[E] = go(p, At(false, false)).runA(from).value._1

    private def go[E](p: Prog[E], at: At): S[(Prog[E], At)] = p match
      case Prog.Call(op, _, _) if op == Prog.leftWins             => State.pure((p, at))
      case Prog.Call(op, _, _)                                     => call(p, op, at)
      case Prog.Read(_) | Prog.Write(_, _) | Prog.Modify(_, _, _) => State.pure((p, at.copy(stepped = true)))
      case Prog.Bind(a, x, r)                                      =>
        go(a, at).flatMap((a1, at1) => go(r, at1).map((r1, at2) => (Prog.Bind(a1, x, r1), at2)))
      case Prog.Let(x, v, r)                     => go(r, at).map((r1, at1) => (Prog.Let(x, v, r1), at1))
      case Prog.Loop(xs, x, b)                   => again(b, at)(Prog.Loop(xs, x, _))
      case Prog.Collect(xs, x, b)                => again(b, at)(Prog.Collect(xs, x, _))
      case Prog.Accumulate(xs, z, a, x, b)       => again(b, at)(Prog.Accumulate(xs, z, a, x, _))
      case Prog.ParEach(xs, x, b, n)             => again(b, at)(Prog.ParEach(xs, x, _, n))
      case Prog.Atomic(b)                        => go(b, at).map((b1, at1) => (Prog.Atomic(b1), at1))
      case Prog.Cut(b)                           => go(b, at).map((b1, at1) => (Prog.Cut(b1), at1))
      case other                                 => sides(other, at)

    /** A step of two sides or more: each read from where the step starts. */
    private def sides[E](p: Prog[E], at: At): S[(Prog[E], At)] = p match
      case Prog.Branch(c, a, b)         =>
        (go(a, at), go(b, at)).mapN { case ((a1, x), (b1, y)) => (Prog.Branch(c, a1, b1), x.or(y)) }
      case Prog.Catch(a, t, x, h)       =>
        (go(a, at), go(h, after(a, at))).mapN { case ((a1, y), (h1, z)) => (Prog.Catch(a1, t, x, h1), y.or(z)) }
      case Prog.Par(l, a, r, b)         =>
        (go(l, at), go(r, at)).mapN { case ((l1, x), (r1, y)) =>
          (Prog.Par(l1, a, r1, b), At(x.stepped || y.stepped, x.looked || y.looked)) }
      case Prog.Race(l, r, reading)     =>
        (go(l, at), go(r, at), go(reading, at)).mapN { case ((l1, _), (r1, _), (q, z)) => (Prog.Race(l1, r1, q), z) }
      case Prog.Guard(b, t, f, reading) =>
        (go(b, at), go(f, after(b, at)), go(reading, at)).mapN { case ((b1, _), (f1, _), (q, z)) =>
          (Prog.Guard(b1, t, f1, q), z) }
      case leaf                         => State.pure((leaf, at))

    /** A step: a late look, or a late call of a program that may look, given a look first. */
    private def call[E](p: Prog[E], op: SymbolName, at: At): S[(Prog[E], At)] =
      val clocks = op == clock.now || op == clock.sleep || op == Prog.reach
      val next = At(stepped = true, looked = at.looked || clocks)
      if (op == clock.now || (!clocks && looking(op))) && at.stepped && !at.looked then
        State(n => (n + 1, (Prog.Bind(Prog.Call(clock.now, Nil, seconds), Binder(VarId.step(n), "looked", seconds),
          p), next)))
      else State.pure((p, next))

    /** A body run any number of times: a later round comes after the steps of an earlier one. */
    private def again[E](b: Prog[E], at: At)(rebuilt: Prog[E] => Prog[E]): S[(Prog[E], At)] =
      val round = after(b, at)
      go(b, round).map((b1, _) => (rebuilt(b1), round))

    /** Where a handler or a finalizer starts: after some of `body`'s steps, the clock perhaps not stepped. */
    private def after[E](body: Prog[E], at: At): At = at.copy(stepped = at.stepped || Progs.all(body).exists {
      case Prog.Call(op, _, _)                                    => op != Prog.leftWins
      case Prog.Read(_) | Prog.Write(_, _) | Prog.Modify(_, _, _) => true
      case _                                                      => false
    })
