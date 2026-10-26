package frflow.core.expr

import cats.syntax.all.*
import frflow.core.name.BoundaryName
import frflow.core.ty.Ty

/** The essential operations of programs: their sequential reading, what they mention, and whether they may fail. */
object Progs:
  /** What a concurrent step means one step at a time; the step itself otherwise. */
  def sequential(p: Prog): Prog = p match
    case Prog.Par(l, a, r, b)      =>
      Prog.Bind(l, a, Prog.Bind(r, b, Prog.Pure(Expr.Tuple(List(Expr.Var(a), Expr.Var(b))))))
    case Prog.ParEach(xs, x, b, _) => Prog.Collect(xs, x, b)
    case Prog.Atomic(b)            => b
    case other                     => other

  /** The steps directly inside `p`, read sequentially. */
  def children(p: Prog): List[Prog] = sequential(p) match
    case Prog.Bind(a, _, r)              => List(a, r)
    case Prog.Let(_, _, r)               => List(r)
    case Prog.Loop(_, _, b)              => List(b)
    case Prog.Collect(_, _, b)           => List(b)
    case Prog.Accumulate(_, _, _, _, b)  => List(b)
    case Prog.Branch(_, a, b)            => List(a, b)
    case Prog.Catch(a, _, _, h)          => List(a, h)
    case _                               => Nil

  def all(p: Prog): List[Prog] = p :: children(p).flatMap(all)

  /** The expressions the steps compute with. */
  def exprs(p: Prog): List[Expr] = all(p).flatMap {
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
    case _                                  => Nil
  }

  def mentions(p: Prog): Mentions = all(p).foldMap {
    case Prog.Call(b, _, _, _) => Mentions.empty.copy(boundaries = List(b))
    case Prog.Read(m)          => Mentions.empty.copy(models = List(m))
    case Prog.Write(m, _)      => Mentions.empty.copy(models = List(m))
    case Prog.Modify(m, _, _)  => Mentions.empty.copy(models = List(m))
    case _                     => Mentions.empty
  }

  def boundaries(p: Prog): List[BoundaryName] = mentions(p).boundaries

  /** Whether the steps may end in an error not handled where it happens: a failing boundary's call, or a raise. */
  def mayFail(p: Prog, failing: BoundaryName => Boolean): Boolean = sequential(p) match
    case Prog.Call(b, _, _, _)  => failing(b)
    case Prog.Raise(_)          => true
    case Prog.Catch(_, _, _, h) => mayFail(h, failing)
    case other                  => children(other).exists(mayFail(_, failing))

  /** The parallel steps (`parTupled`, `parTraverse`), in order: each gives a `commute_i` obligation. */
  def parallel(p: Prog): List[Prog] = (p :: concurrentChildren(p)).filter {
    case Prog.Par(_, _, _, _) | Prog.ParEach(_, _, _, _) => true
    case _                                             => false
  }

  private def concurrentChildren(p: Prog): List[Prog] = (p match
    case Prog.Par(l, _, r, _)       => List(l, r)
    case Prog.ParEach(_, _, b, _)   => List(b)
    case Prog.Atomic(b)             => List(b)
    case other                      => children(other)
  ).flatMap(c => c :: concurrentChildren(c))

  /** The error types raised or handled. */
  def errors(p: Prog): List[Ty] = all(p).collect {
    case Prog.Raise(e)          => Exprs.typeOf(e)
    case Prog.Catch(_, t, _, _) => t
  }.distinct
