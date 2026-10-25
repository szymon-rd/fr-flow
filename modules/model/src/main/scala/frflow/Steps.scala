package frflow

import frflow.program.Lambdas
import frflow.types.Shape
import java.lang.reflect.Method

/** A flow built once on symbolic values: what Lean prints and Scala runs. */
private[frflow] enum Steps:
  case Ret(t: Tree)
  case Op(boundary: Boundary[?], method: Method, args: List[Tree])
  /** `let b ← first; rest` (`b` unused when a wildcard). */
  case Seq(first: Steps, b: Binder, rest: Steps)
  case Loop(xs: Tree, b: Binder, body: Steps)
  /** `xs.mapM fun b => body`: each element in turn, the results in a list (`traverse`). */
  case Collect(xs: Tree, b: Binder, body: Steps)
  /** `xs.foldlM (init := z) fun acc b => body` (`foldM`). */
  case Accumulate(xs: Tree, z: Tree, acc: Binder, b: Binder, body: Steps)
  case Branch(c: Tree, a: Steps, b: Steps)
  case Read(model: StateModel[?])
  case Write(model: StateModel[?], s: Tree)
  case Modify(model: StateModel[?], b: Binder, body: Tree)
  case Outside(run: () => Any)
  /** `let b := v; rest`: a value the program named (`t = …` in a for-comprehension), computed once. */
  case Let(b: Binder, v: Tree, rest: Steps)
  /** `throwThe E e`. */
  case Raise(e: Tree, err: LeanType[?])
  /** `tryCatchThe E (do body) (fun b => do handler)`. */
  case Catch(body: Steps, err: LeanType[?], b: Binder, handler: Steps)
  /** Flows at once, or a transaction, or a finalizer kept on cancellation: what Lean, the models and a sequential run
    * read is `Steps.reading` of it (the branches in turn, the body); only a concurrent run (`Flows.run` in a
    * `GenConcurrent`, IO) runs the branches at once.
    */
  /** `parTupled`: read as `let a ← left; let b ← right; pure (a, b)`. */
  case Par(left: Steps, a: Binder, right: Steps, b: Binder)
  /** `parTraverseN`: read as `Collect`. */
  case ParEach(xs: Tree, b: Binder, body: Steps, limit: Option[Int], out: LeanType[?])
  /** `atomically`: read as its body. */
  case Atomic(body: Steps)
  /** `race`: read as `reading` (the scheduler's choice of the winner, `Races`). */
  case Race(left: Steps, right: Steps, reading: Steps)
  /** `guarantee`: read as `reading` (the finalizer after a result, and before an error is raised again). */
  case Guard(body: Steps, err: LeanType[?], fin: Steps, reading: Steps)

private[frflow] object Steps:
  /** The steps of a flow, and the type of its result. */
  def of(f: Flow[?]): (Steps, LeanType[?]) = within(f, Nil)

  /** What a concurrent step means one step at a time: the branches in turn, the transaction's body; `None` of others. */
  def reading(s: Steps): Option[Steps] = s match
    case Par(l, a, r, b)       => Some(Seq(l, a, Seq(r, b, Ret(Tree.Tup(List(Tree.Var(a), Tree.Var(b)))))))
    case ParEach(xs, b, body, _, _) => Some(Collect(xs, b, body))
    case Atomic(body)          => Some(body)
    case Race(_, _, r)         => Some(r)
    case Guard(_, _, _, r)     => Some(r)
    case _                     => None
  /** The steps with every concurrent step read as `reading` says. */
  def sequential(s: Steps): Steps = reading(s).getOrElse(s)

  /** Whether the steps may end in an error: a failing boundary's call, or a raise, not handled where it happens. */
  def mayFail(s: Steps): Boolean = s match
    case Op(b, _, _)           => b.fails
    case Raise(_, _)           => true
    case Catch(_, _, _, h)     => mayFail(h)
    case Seq(a, _, r)          => mayFail(a) || mayFail(r)
    case Loop(_, _, b)         => mayFail(b)
    case Collect(_, _, b)      => mayFail(b)
    case Accumulate(_, _, _, _, b) => mayFail(b)
    case Branch(_, a, b)       => mayFail(a) || mayFail(b)
    case Let(_, _, r)          => mayFail(r)
    case other                 => reading(other).exists(mayFail)

  private def concurrent(s: Steps): Boolean = fold(s, false)((acc, x) => acc || PartialFunction.cond(x) {
    case Par(_, _, _, _) | ParEach(_, _, _, _, _) | Atomic(_) | Race(_, _, _) => true
  })
  /** Whether the steps run branches at once (`parTupled`, `parTraverse`, `race`). */
  def parallel(s: Steps): Boolean = fold(s, false)((acc, x) => acc || PartialFunction.cond(x) {
    case Par(_, _, _, _) | ParEach(_, _, _, _, _) | Race(_, _, _) => true
  })
  /** Whether the steps race: who wins is the scheduler's, so a run is compared with the contract, not with the models. */
  def racing(s: Steps): Boolean = fold(s, false)((acc, x) => acc || x.isInstanceOf[Race])

  /** A value the program named and later steps use (`t = expire(s, now)` is a `val t` their lambdas capture) is
    * computed once, in a `let` named as the program names it, where the flow that first uses it begins; `bound`
    * holds those already let above.
    */
  private def within(f: Flow[?], bound: List[Tree]): (Steps, LeanType[?]) =
    val named = shared(f).foldLeft(List.empty[(String, Term[?])]) { (acc, x) =>
      if (bound ++ acc.map(_._2.termTree)).exists(_ eq x._2.termTree) then acc else acc :+ x
    }
    val (s, t) = build(f, bound ++ named.map(_._2.termTree))
    val used = named.filter((_, x) => Trees.occurs(x.termTree, s))
    // One named from another comes after it.
    val ordered = used.sortBy((_, x) => used.count((_, y) => (y ne x) && Trees.occurs(y.termTree, x.termTree)))
    (ordered.foldRight(s) { case ((n, x), acc) =>
      val b = Binder(n, x.termType)
      Let(b, x.termTree, Trees.replaceIn(acc, x.termTree, Tree.Var(b)))
    }, t)

  /** The compound terms the lambdas of `f` capture (a named value, not a variable or a constant). */
  private def shared(f: Flow[?]): List[(String, Term[?])] =
    def captures(g: AnyRef) = Lambdas.captured(g).collect {
      case (n, x: Term[?]) if (x.termTree match { case Tree.Var(_) | Tree.Lit(_, _) | Tree.Ref(_) => false; case _ => true }) => (n, x)
    }
    f match
      case Flow.Bind(first, _, named) => shared(first) ++ captures(named)
      case Flow.Each(_, body)         => captures(body)
      case Flow.EachResult(_, body)   => captures(body)
      case Flow.Fold(_, _, body)      => captures(body)
      case Flow.Cond(_, a, b)         => shared(a) ++ shared(b)
      case Flow.Catch(first, h, _)    => shared(first) ++ captures(h)
      case Flow.Attempt(first, _)     => shared(first)
      case Flow.Guard(body, fin, _)   => shared(body) ++ shared(fin)
      case Flow.Par(l, r)             => shared(l) ++ shared(r)
      case Flow.ParEach(_, body, _)   => captures(body)
      case Flow.Atomic(body)          => shared(body)
      case Flow.Race(l, r)            => shared(l) ++ shared(r)
      case Flow.Update(_, g)          => captures(g)
      case _                          => Nil

  private def build(f: Flow[?], bound: List[Tree]): (Steps, LeanType[?]) = f match
    case Flow.Pure(t)          => (Ret(t.termTree), t.termType)
    case c @ Flow.Call(b, m, args) => (Op(b, m, args.map(_.termTree)), LeanType.ofJava(m.getGenericReturnType))
    case Flow.Bind(first, next, named) =>
      val (s, t) = within(first, bound)
      val b = Lambda.binders(named, List(t)).head
      val (rest, r) = within(next.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (Seq(s, b, rest), r)
    case Flow.Each(xs, body)   =>
      val elem = xs.termType.shape match { case Shape.ListOf(a) => a; case _ => LeanType.unknown }
      val b = Lambda.binders(body, List(elem)).head
      val (s, t) = within(body.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      // A loop's body yields nothing: a result of another type is dropped.
      val unitBody = if t.shape == Shape.UnitT then s else Seq(s, Binder("_$", t), Ret(Tree.Lit((), summon[LeanType[Unit]])))
      (Loop(xs.termTree, b, unitBody), summon[LeanType[Unit]])
    case Flow.EachResult(xs, body) =>
      val b = Lambda.binders(body, List(elemOf(xs))).head
      val (s, t) = within(body.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (Collect(xs.termTree, b, s), LeanType.of(Shape.ListOf(t)))
    case Flow.Fold(xs, z, body) =>
      val List(acc, b) = Lambda.binders(body, List(z.termType, elemOf(xs))): @unchecked
      val (s, _) = within(body.asInstanceOf[(Term[Any], Term[Any]) => Flow[?]](acc.term, b.term), bound)
      (Accumulate(xs.termTree, z.termTree, acc, b, s), z.termType)
    case Flow.Cond(c, a, b)    =>
      val (sa, t) = within(a, bound)
      val (sb, u) = within(b, bound)
      (Branch(c.termTree, sa, sb), known(t, u))
    case Flow.Raise(e)         => (Raise(e.termTree, e.termType), LeanType.unknown)
    case Flow.Catch(first, h, err) =>
      val (s, t) = within(first, bound)
      val b = Lambda.binders(h, List(err)).head
      val (hs, u) = within(h.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (Catch(s, err, b, hs), known(t, u))
    case Flow.Attempt(first, err) =>
      val (s, t) = within(first, bound)
      val (a, e) = (Binder("a", t), Binder("e", err))
      (Catch(Seq(s, a, Ret(Tree.Inj(false, Tree.Var(a)))), err, e, Ret(Tree.Inj(true, Tree.Var(e)))), LeanType.of(Shape.EitherOf(err, t)))
    case Flow.Get(m)           => (Read(m), m.stateType)
    case Flow.Put(m, s)        => (Write(m, s.termTree), summon[LeanType[Unit]])
    case Flow.Update(m, f)     =>
      val b = Lambda.binders(f, List(m.stateType)).head
      (Modify(m, b, f.asInstanceOf[Term[Any] => Term[Any]](b.term).termTree), summon[LeanType[Unit]])
    case Flow.Effect(run)      => (Outside(run), LeanType.unknown)
    case Flow.Guard(body, fin, err) =>
      val (s, t) = within(body, bound)
      val (f, _) = within(fin, bound)
      val reading = body.handleErrorWith[Any](e => fin.flatMap(_ => Flow.raiseError(e)))(using err.asInstanceOf[LeanType[Any]]).flatMap(a => fin.map(_ => a))
      (Guard(s, err, f, within(reading, bound)._1), t)
    case Flow.Par(l, r) =>
      val (sl, tl) = within(l, bound)
      val (sr, tr) = within(r, bound)
      (Par(sl, Binder("left", tl), sr, Binder("right", tr)), LeanType.of(Shape.TupleOf(List(tl, tr))))
    case Flow.ParEach(xs, body, limit) =>
      val b = Lambda.binders(body, List(elemOf(xs))).head
      val (s, t) = within(body.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (ParEach(xs.termTree, b, s, limit, t), LeanType.of(Shape.ListOf(t)))
    case Flow.Atomic(body) =>
      val (s, t) = within(body, bound)
      if concurrent(s) then throw IllegalArgumentException(
        "FrFlow: a transaction (atomically) holds no transaction, parallel branch or race inside it: it is one step of the world")
      (Atomic(s), t)
    case Flow.Race(l, r) =>
      val (sl, tl) = within(l, bound)
      val (sr, tr) = within(r, bound)
      (Race(sl, sr, raceReading(sl, tl, sr, tr)), LeanType.of(Shape.EitherOf(tl, tr)))

  /** A race one step at a time: the scheduler says which side finishes first (`Races.leftFirst`); the winner runs and
    * gives the result. The loser is cancelled: it leaves nothing, or, when it is one transaction (which once begun runs
    * to its end), it may have committed before the winner finished (`Races.committed`).
    */
  private def raceReading(l: Steps, tl: LeanType[?], r: Steps, tr: LeanType[?]): Steps =
    val bool = summon[LeanType[Boolean]]
    val unit = Ret(Tree.Lit((), summon[LeanType[Unit]]))
    def pick(m: java.lang.reflect.Method) = Op(Races.boundary, m, Nil)
    def wins(winner: Steps, t: LeanType[?], left: Boolean, loser: Steps): Steps =
      val x = Binder(if left then "won" else "wonRight", t)
      val result = Seq(winner, x, Ret(Tree.Inj(left, Tree.Var(x))))
      loser match
        case Atomic(_) =>
          val c = Binder("committed", bool)
          Seq(pick(Races.committed), c, Seq(Branch(Tree.Var(c), Seq(loser, Binder("_$", LeanType.unknown), unit), unit), Binder("_$", summon[LeanType[Unit]]), result))
        case _ => result
    val first = Binder("leftFirst", bool)
    Seq(pick(Races.leftFirst), first, Branch(Tree.Var(first), wins(l, tl, true, r), wins(r, tr, false, l)))

  /** A flow's type, from either side: a side that raises has none. */
  private def known(t: LeanType[?], u: LeanType[?]): LeanType[?] = if t.shape == Shape.Unknown then u else t

  private def elemOf(xs: Term[?]): LeanType[?] = xs.termType.shape match { case Shape.ListOf(a) => a; case _ => LeanType.unknown }

  def fold[A](s: Steps, z: A)(f: (A, Steps) => A): A =
    val here = f(z, s)
    s match
      case Seq(a, _, b)    => fold(b, fold(a, here)(f))(f)
      case Loop(_, _, b)   => fold(b, here)(f)
      case Collect(_, _, b) => fold(b, here)(f)
      case Accumulate(_, _, _, _, b) => fold(b, here)(f)
      case Branch(_, a, b) => fold(b, fold(a, here)(f))(f)
      case Let(_, _, r)    => fold(r, here)(f)
      case Catch(a, _, _, b) => fold(b, fold(a, here)(f))(f)
      case other           => reading(other).fold(here)(fold(_, here)(f))

  def boundaries(s: Steps): List[Boundary[?]] = fold(s, List.empty[Boundary[?]]) {
    case (acc, Op(b, _, _)) if !acc.contains(b) => acc :+ b
    case (acc, _)                               => acc
  }
  def effectful(s: Steps): Boolean = fold(s, false)((acc, x) => acc || x.isInstanceOf[Outside])
  /** The types of the errors the steps raise or handle. */
  def errors(s: Steps): List[LeanType[?]] = fold(s, List.empty[LeanType[?]]) {
    case (acc, Raise(_, e))       => acc :+ e
    case (acc, Catch(_, e, _, _)) => acc :+ e
    case (acc, _)                 => acc
  }
