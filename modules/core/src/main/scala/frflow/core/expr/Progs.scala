package frflow.core.expr

import cats.syntax.all.*
import frflow.core.name.SymbolName
import frflow.core.ty.Ty

/** The essential operations of programs: their sequential reading, their terms, what they mention, whether they may
  * fail. Over any term representation `E`, but `errors` and `failsWith`, which read the IR's types.
  */
object Progs:
  /** What a concurrent step means one step at a time; the step itself otherwise. */
  def sequential[E](p: Prog[E])(using pairs: Prog.Pairs[E]): Prog[E] = p match
    case Prog.Par(l, a, r, b)      => Prog.Bind(l, a, Prog.Bind(r, b, Prog.Pure(pairs.pair(a, b))))
    case Prog.ParEach(xs, x, b, _) => Prog.Collect(xs, x, b)
    case Prog.Atomic(b)            => b
    case Prog.Race(_, _, reading)  => reading
    case Prog.Guard(_, _, _, r)    => r
    case other                     => other

  /** The steps directly inside `p`, read sequentially (a pair's reading is structural: no term is needed). */
  def children[E](p: Prog[E]): List[Prog[E]] = p match
    case Prog.Bind(a, _, r)              => List(a, r)
    case Prog.Let(_, _, r)               => List(r)
    case Prog.Loop(_, _, b)              => List(b)
    case Prog.Collect(_, _, b)           => List(b)
    case Prog.Accumulate(_, _, _, _, b)  => List(b)
    case Prog.Branch(_, a, b)            => List(a, b)
    case Prog.Catch(a, _, _, h)          => List(a, h)
    case Prog.Par(l, _, r, _)            => List(l, r)
    case Prog.ParEach(_, _, b, _)        => List(b)
    case Prog.Atomic(b)                  => List(b)
    case Prog.Cut(b)                     => List(b)
    case Prog.Race(_, _, reading)        => List(reading)
    case Prog.Guard(_, _, _, reading)    => List(reading)
    case _                               => Nil

  def all[E](p: Prog[E]): List[Prog[E]] = p :: children(p).flatMap(all)

  /** Every variable the steps bind, in their structure and in their terms. */
  def binders(p: Prog[Expr]): List[Binder] = all(p).flatMap(bound) ++ terms(p).flatMap(Exprs.all).flatMap(Exprs.binders)

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

  /** The terms the steps compute with. */
  def terms[E](p: Prog[E]): List[E] = all(p).flatMap {
    case Prog.Pure(t)                       => List(t)
    case Prog.Call(_, as, _)                => as
    case Prog.Let(_, v, _)                  => List(v)
    case Prog.Loop(xs, _, _)                => List(xs)
    case Prog.Collect(xs, _, _)             => List(xs)
    case Prog.Accumulate(xs, z, _, _, _)    => List(xs, z)
    case Prog.Branch(c, _, _)               => List(c)
    case Prog.Write(_, s)                   => List(s)
    case Prog.Modify(_, _, s)               => List(s)
    case Prog.Raise(e)                      => List(e)
    case Prog.ParEach(xs, _, _, _)          => List(xs)
    case _                                  => Nil
  }

  def mentions[E](p: Prog[E]): Mentions = all(p).foldMap {
    case Prog.Call(op, _, _)   => Mentions.empty.copy(operations = List(op))
    case Prog.Read(m)          => Mentions.empty.copy(models = List(m))
    case Prog.Write(m, _)      => Mentions.empty.copy(models = List(m))
    case Prog.Modify(m, _, _)  => Mentions.empty.copy(models = List(m))
    case _                     => Mentions.empty
  }

  /** The operations on a state the steps call, each once. */
  def operations[E](p: Prog[E]): List[SymbolName] = mentions(p).operations

  /** The error types the steps may end in, each once: those raised, and those of the operations called whose
    * model may fail (`failing`), outside a handler of that type.
    */
  def failsWith(p: Prog[Expr], failing: SymbolName => Option[Ty]): List[Ty] =
    def go(q: Prog[Expr], caught: Set[Ty]): List[Ty] = q match
      case Prog.Call(op, _, _)    => failing(op).filterNot(caught).toList
      case Prog.Raise(e)          => Option(Exprs.typeOf(e)).filterNot(caught).toList
      case Prog.Catch(a, t, _, h) => go(a, caught + t) ++ go(h, caught)
      case other                  => children(other).flatMap(go(_, caught))
    go(p, Set.empty).distinct

  /** Whether a transaction holds another (`Atomic` inside `Atomic`). */
  def nestsAtomic[E](p: Prog[E]): Boolean = all(p).exists {
    case Prog.Atomic(body) => all(body).exists {
        case Prog.Atomic(_) => true
        case _              => false
      }
    case _                 => false
  }

  /** Whether the steps race two branches. */
  def races[E](p: Prog[E]): Boolean = all(p).exists {
    case Prog.Race(_, _, _) => true
    case _                  => false
  }

  /** Whether a race's side holds a race, a pair at once (`parTupled`) or a finalizer (`guarantee`, `bracket`): its
    * loser is read cancelled between two of its steps (each branch of a traverse at once at its own), and neither a
    * finalizer run then nor a race or a pair in it is read.
    */
  def holdsInSide[E](p: Prog[E]): Boolean = all(p).exists {
    case Prog.Race(l, r, _) => List(l, r).exists(side => all(side).exists {
        case Prog.Race(_, _, _) | Prog.Guard(_, _, _, _) | Prog.Par(_, _, _, _) => true
        case _                                                                => false
      })
    case _                  => false
  }

  /** The error types raised or handled, read off the IR. */
  def errors(p: Prog[Expr]): List[Ty] = all(p).collect {
    case Prog.Raise(e)          => Exprs.typeOf(e)
    case Prog.Catch(_, t, _, _) => t
  }.distinct

  /** The same steps over other terms: the IR of a recorded program (`Written.steps`, through `ToExpr`). */
  def map[E, F](p: Prog[E])(f: E => F): Prog[F] = p match
    case Prog.Pure(t)                   => Prog.Pure(f(t))
    case Prog.Call(op, as, t)           => Prog.Call(op, as.map(f), t)
    case Prog.Bind(a, x, r)             => Prog.Bind(map(a)(f), x, map(r)(f))
    case Prog.Let(x, v, r)              => Prog.Let(x, f(v), map(r)(f))
    case Prog.Loop(xs, x, b)            => Prog.Loop(f(xs), x, map(b)(f))
    case Prog.Collect(xs, x, b)         => Prog.Collect(f(xs), x, map(b)(f))
    case Prog.Accumulate(xs, z, a, x, b) => Prog.Accumulate(f(xs), f(z), a, x, map(b)(f))
    case Prog.Branch(c, a, b)           => Prog.Branch(f(c), map(a)(f), map(b)(f))
    case Prog.Read(m)                   => Prog.Read(m)
    case Prog.Write(m, s)               => Prog.Write(m, f(s))
    case Prog.Modify(m, x, n)           => Prog.Modify(m, x, f(n))
    case Prog.Raise(e)                  => Prog.Raise(f(e))
    case Prog.Catch(b, t, x, h)         => Prog.Catch(map(b)(f), t, x, map(h)(f))
    case Prog.Par(l, a, r, b)           => Prog.Par(map(l)(f), a, map(r)(f), b)
    case Prog.Race(l, r, reading)       => Prog.Race(map(l)(f), map(r)(f), map(reading)(f))
    case Prog.Guard(b, t, fin, reading) => Prog.Guard(map(b)(f), t, map(fin)(f), map(reading)(f))
    case Prog.ParEach(xs, x, b, n)      => Prog.ParEach(f(xs), x, map(b)(f), n)
    case Prog.Atomic(b)                 => Prog.Atomic(map(b)(f))
    case Prog.Cut(b)                    => Prog.Cut(map(b)(f))
