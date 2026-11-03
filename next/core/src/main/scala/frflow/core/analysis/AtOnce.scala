package frflow.core.analysis

import frflow.core.expr.{Expr, Prog, Progs}
import frflow.core.name.ModelName
import frflow.core.vocab.Vocabulary

/** Concurrent steps as production interleaves them (ARCHITECTURE 4.4): a pair's two branches, a traverse's body beside
  * itself (two of its elements), a race's two sides. A side interleaves at its steps: each operation's call, and each
  * transaction whole, which only another transaction waits for (the one lock), so that a call outside one may come
  * between the calls inside it. Lean reads the sides in turn; that stands for every interleaving when each step of
  * one side commutes with each step of the other (Lipton): `commute_i` asks it of each pair touching a model in
  * common (`pairs`), as steps on disjoint models commute by construction.
  */
object AtOnce:
  /** The concurrent steps of a program, outermost first: a race's and a finalizer's steps as written, not their
    * readings.
    */
  def of[E](p: Prog[E]): List[Prog[E]] = p match
    case Prog.Par(l, _, r, _)     => p :: of(l) ++ of(r)
    case Prog.ParEach(_, _, b, _) => p :: of(b)
    case Prog.Race(l, r, _)       => p :: of(l) ++ of(r)
    case Prog.Guard(b, _, f, _)   => of(b) ++ of(f)
    case other                    => Progs.children(other).flatMap(of)

  /** A concurrent step's two sides: a traverse's body twice, two of its elements. */
  def sides[E](k: Prog[E]): Option[(Prog[E], Prog[E])] = k match
    case Prog.Par(l, _, r, _)     => Some((l, r))
    case Prog.ParEach(_, _, b, _) => Some((b, b))
    case Prog.Race(l, r, _)       => Some((l, r))
    case _                        => None

  /** A side's steps, in order: each call of an operation and each transaction, whole; then the calls inside each
    * transaction (`units` numbers both).
    */
  def units[E](side: Prog[E]): List[Prog[E]] = steps(side) ++ inner(side)

  /** Each pair of steps, one of each side of the concurrent step `k`, by their place in `units`, that may interleave
    * and touch a model in common: two transactions, two calls, or a call and one inside a transaction of the other
    * side; each pair once (of a traverse, either way round).
    */
  def pairs(v: Vocabulary, k: Prog[Expr]): List[(Int, Int)] = sides(k).toList.flatMap { (a, b) =>
    val (ua, ub) = (units(a), units(b))
    val meeting = for
      i <- ua.indices.toList
      j <- ub.indices.toList
      if meet(i < steps(a).size, ua(i), j < steps(b).size, ub(j)) && models(v, ua(i)).exists(models(v, ub(j)))
    yield (i, j)
    val alike = k match
      case Prog.ParEach(_, _, _, _) => (i: Int, j: Int) => Set(ua(i), ub(j))
      case _                        => (i: Int, j: Int) => (ua(i), ub(j))
    meeting.distinctBy(alike.tupled)
  }

  /** Every pair of a program's concurrent steps, numbered across them: the concurrent step's place in `of`, then
    * the pair's.
    */
  def all(v: Vocabulary, p: Prog[Expr]): List[(Int, (Int, Int))] =
    of(p).zipWithIndex.flatMap((k, n) => pairs(v, k).map(n -> _))

  /** Whether a concurrent step lets an error out of a side while another runs on: a pair's branch that may fail
    * beside one that may fail or changes a model's state, or a traverse's body that may fail. Production cancels
    * the others then, at whatever step each has reached, which the reading in turn does not read.
    */
  def failsBeside(v: Vocabulary, p: Prog[Expr]): Boolean = of(p).exists {
    case Prog.Par(l, _, r, _)     => (fails(v, l) && !quiet(v, r)) || (fails(v, r) && !quiet(v, l))
    case Prog.ParEach(_, _, b, _) => fails(v, b)
    case _                        => false
  }

  private def steps[E](p: Prog[E]): List[Prog[E]] = p match
    case Prog.Call(op, _, _)                                     => if op == Prog.leftWins then Nil else List(p)
    case Prog.Atomic(_) | Prog.Read(_) | Prog.Write(_, _) | Prog.Modify(_, _, _) => List(p)
    case Prog.Race(l, r, _)                                      => steps(l) ++ steps(r)
    case Prog.Guard(b, _, f, _)                                  => steps(b) ++ steps(f)
    case other                                                   => Progs.children(other).flatMap(steps)

  private def inner[E](p: Prog[E]): List[Prog[E]] = steps(p).flatMap {
    case Prog.Atomic(b) => steps(b)
    case _              => Nil
  }

  /** Two steps interleave: two transactions, two calls outside one, or a call and one inside the other's. */
  private def meet[E](topA: Boolean, a: Prog[E], topB: Boolean, b: Prog[E]): Boolean = (topA, topB) match
    case (true, true)   => atomic(a) == atomic(b)
    case (false, true)  => !atomic(b)
    case (true, false)  => !atomic(a)
    case (false, false) => false

  private def atomic[E](p: Prog[E]): Boolean = p match
    case Prog.Atomic(_) => true
    case _              => false

  /** The models a step touches. */
  private def models[E](v: Vocabulary, p: Prog[E]): Set[ModelName] = p match
    case Prog.Call(op, _, _)     => v.modelOf(op).map(_.name).toSet
    case Prog.Atomic(b)          => steps(b).flatMap(models(v, _)).toSet
    case Prog.Read(m)            => Set(m)
    case Prog.Write(m, _)        => Set(m)
    case Prog.Modify(m, _, _)    => Set(m)
    case _                       => Set.empty

  private def fails(v: Vocabulary, p: Prog[Expr]): Boolean =
    Progs.failsWith(p, v.modelOf(_).flatMap(_.failsWith)).nonEmpty

  /** A side that cannot fail and changes no model's state: cut short, it has done nothing a statement reads. */
  private def quiet(v: Vocabulary, p: Prog[Expr]): Boolean = !fails(v, p) && !Progs.all(p).exists {
    case Prog.Call(op, _, _)                  => v.modelOf(op).flatMap(_.op(op)).exists(o => writes(o.steps))
    case Prog.Write(_, _) | Prog.Modify(_, _, _) => true
    case _                                    => false
  }

  private def writes[E](p: Prog[E]): Boolean = Progs.all(p).exists {
    case Prog.Write(_, _) | Prog.Modify(_, _, _) => true
    case _                                    => false
  }
