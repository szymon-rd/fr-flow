package frflow.core.expr

import cats.syntax.all.*
import frflow.core.name.BoundaryName
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
    case Prog.Race(_, _, reading)        => List(reading)
    case Prog.Guard(_, _, _, reading)    => List(reading)
    case _                               => Nil

  def all[E](p: Prog[E]): List[Prog[E]] = p :: children(p).flatMap(all)

  /** The terms the steps compute with. */
  def terms[E](p: Prog[E]): List[E] = all(p).flatMap {
    case Prog.Pure(t)                       => List(t)
    case Prog.Call(_, _, as, _)             => as
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
    case Prog.Call(b, _, _, _) => Mentions.empty.copy(boundaries = List(b))
    case Prog.Read(m)          => Mentions.empty.copy(models = List(m))
    case Prog.Write(m, _)      => Mentions.empty.copy(models = List(m))
    case Prog.Modify(m, _, _)  => Mentions.empty.copy(models = List(m))
    case _                     => Mentions.empty
  }

  def boundaries[E](p: Prog[E]): List[BoundaryName] = mentions(p).boundaries

  /** The error types the steps may end in, each once: those raised, and those of the failing boundaries called
    * (`failing`), outside a handler of that type.
    */
  def failsWith(p: Prog[Expr], failing: BoundaryName => Option[Ty]): List[Ty] =
    def go(q: Prog[Expr], caught: Set[Ty]): List[Ty] = q match
      case Prog.Call(b, _, _, _)  => failing(b).filterNot(caught).toList
      case Prog.Raise(e)          => Option(Exprs.typeOf(e)).filterNot(caught).toList
      case Prog.Catch(a, t, _, h) => go(a, caught + t) ++ go(h, caught)
      case other                  => children(other).flatMap(go(_, caught))
    go(p, Set.empty).distinct

  /** The parallel steps (`parTupled`, `parTraverse`), in order: each gives a `commute_i` obligation. */
  def parallel[E](p: Prog[E]): List[Prog[E]] = all(p).filter {
    case Prog.Par(_, _, _, _) | Prog.ParEach(_, _, _, _) => true
    case _                                             => false
  }

  /** The error types raised or handled, read off the IR. */
  def errors(p: Prog[Expr]): List[Ty] = all(p).collect {
    case Prog.Raise(e)          => Exprs.typeOf(e)
    case Prog.Catch(_, t, _, _) => t
  }.distinct

  /** The same steps over other terms: the IR of a recorded program (`Written.steps`, through `ToExpr`). */
  def map[E, F](p: Prog[E])(f: E => F): Prog[F] =
    def apply(q: Prog[E]): Prog[F] = q match
      case Prog.Pure(t)                   => Prog.Pure(f(t))
      case Prog.Call(b, op, as, t)        => Prog.Call(b, op, as.map(f), t)
      case Prog.Bind(a, x, r)             => Prog.Bind(apply(a), x, apply(r))
      case Prog.Let(x, v, r)              => Prog.Let(x, f(v), apply(r))
      case Prog.Loop(xs, x, b)            => Prog.Loop(f(xs), x, apply(b))
      case Prog.Collect(xs, x, b)         => Prog.Collect(f(xs), x, apply(b))
      case Prog.Accumulate(xs, z, a, x, b) => Prog.Accumulate(f(xs), f(z), a, x, apply(b))
      case Prog.Branch(c, a, b)           => Prog.Branch(f(c), apply(a), apply(b))
      case Prog.Read(m)                   => Prog.Read(m)
      case Prog.Write(m, s)               => Prog.Write(m, f(s))
      case Prog.Modify(m, x, n)           => Prog.Modify(m, x, f(n))
      case Prog.Raise(e)                  => Prog.Raise(f(e))
      case Prog.Catch(b, t, x, h)         => Prog.Catch(apply(b), t, x, apply(h))
      case Prog.Par(l, a, r, b)           => Prog.Par(apply(l), a, apply(r), b)
      case Prog.Race(l, r, reading)       => Prog.Race(apply(l), apply(r), apply(reading))
      case Prog.Guard(b, t, fin, reading) => Prog.Guard(apply(b), t, apply(fin), apply(reading))
      case Prog.ParEach(xs, x, b, n)      => Prog.ParEach(f(xs), x, apply(b), n)
      case Prog.Atomic(b)                 => Prog.Atomic(apply(b))
    apply(p)
