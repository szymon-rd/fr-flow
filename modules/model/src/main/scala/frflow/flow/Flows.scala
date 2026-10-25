package frflow
package flow

import frflow.types.Shape

/** Running flows: on the models (the proofs' world, held in Scala), and in production (any `Sync`). */
private[frflow] object Flows:
  import Eval.Env

  /** A flow on the models that failed with `error`, in the world `at` as it was then. */
  final case class Raised(error: Any, at: World) extends RuntimeException(s"the flow failed with $error", null, false, false)

  /** The types of the errors a flow's run may end in: those it raises or handles, and its failing boundaries'. */
  def errorTypes(s: Steps): List[LeanType[?]] =
    (Steps.errors(s) ++ Steps.boundaries(s).flatMap(_.failure.map(_.termType))).distinctBy(t => Types.walk(t).lean)

  /** Whether an error is one of type `t`: what a handler of `t` handles. */
  def handles(t: LeanType[?], error: Any): Boolean = t.shape match
    case Shape.Data(adt) => adt.cls.isInstance(error)
    case Shape.Str       => error.isInstanceOf[String]
    case Shape.Num(_)    => error.isInstanceOf[Int] || error.isInstanceOf[Long] || error.isInstanceOf[BigInt]
    case _               => true

  /** The flow on the models: its result and the world after; `Raised` when it fails. A call goes to the model of its
    * boundary; a call of a failing boundary takes the next of the world's faults, and fails, changing nothing, on `true`.
    */
  def onModels(s: Steps, env: Env, w: World): (Any, World) = s match
    case Steps.Ret(t)            => (Eval.compile(t)(env), w)
    case Steps.Op(b, m, args)    =>
      val model = w.parts.keys.find(x => b.cls.isInstance(x))
        .getOrElse(throw IllegalStateException(s"FrFlow: no model of the boundary ${b.name} in $w"))
      val w0 = b.failure.fold(w) { e =>
        val rest = w.withFaults(w.faults.drop(1))
        if w.faults.headOption.contains(true) then throw Raised(Eval.compile(e.termTree)(Map.empty), rest)
        rest
      }
      // Typed as the operation takes them: a model may read their fields.
      val typed = args.zip(m.getGenericParameterTypes.toList).map { (a, t) =>
        val lt = LeanType.ofJava(t)
        Term(Tree.Lit(Eval.compile(a)(env), lt), lt)
      }
      val inner = Steps.of(m.invoke(model, typed*).asInstanceOf[Flow[?]])._1
      val (r, own) = onModel(inner, model, w0(model.asInstanceOf[StateModel[Any]]))
      (r, w0.updated(model, own))
    case Steps.Raise(e, _)       => throw Raised(Eval.compile(e)(env), w)
    case Steps.Catch(body, t, b, handler) =>
      try onModels(body, env, w)
      catch case Raised(err, at) if handles(t, err) => onModels(handler, env + (b -> err), at)
    case Steps.Seq(a, b, rest)   => val (x, w1) = onModels(a, env, w); onModels(rest, env + (b -> x), w1)
    case Steps.Let(b, v, rest)   => onModels(rest, env + (b -> Eval.compile(v)(env)), w)
    case Steps.Loop(xs, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(((): Any, w))((acc, x) => (((), onModels(body, env + (b -> x), acc._2)._2)))
    case Steps.Collect(xs, b, body) =>
      val (ys, w1) = Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Vector.empty[Any], w)) { case ((ys, wi), x) =>
        val (y, wj) = onModels(body, env + (b -> x), wi); (ys :+ y, wj)
      }
      (ys.toList, w1)
    case Steps.Accumulate(xs, z, acc, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Eval.compile(z)(env), w)) { case ((a, wi), x) =>
        onModels(body, env + (acc -> a) + (b -> x), wi)
      }
    case Steps.Branch(c, a, b)   => if Eval.compile(c)(env).asInstanceOf[Boolean] then onModels(a, env, w) else onModels(b, env, w)
    // Branches at once, on the models: in turn, as Lean reads them (the proofs show the order does not matter).
    case other if Steps.reading(other).isDefined => onModels(Steps.sequential(other), env, w)
    case other                   => throw IllegalStateException(s"FrFlow: a proven flow takes no step of a model's own ($other)")

  /** A model's own operation, on its state. */
  private[frflow] def onModel(s: Steps, model: StateModel[?], st: Any, env: Env = Map.empty): (Any, Any) = s match
    case Steps.Ret(t)              => (Eval.compile(t)(env), st)
    case Steps.Read(_)             => (st, st)
    case Steps.Write(_, t)         => ((), Eval.compile(t)(env))
    case Steps.Modify(_, b, body)  => ((), Eval.compile(body)(env + (b -> st)))
    case Steps.Seq(a, b, rest)     => val (x, st1) = onModel(a, model, st, env); onModel(rest, model, st1, env + (b -> x))
    case Steps.Let(b, v, rest)     => onModel(rest, model, st, env + (b -> Eval.compile(v)(env)))
    case Steps.Loop(xs, b, body)   =>
      ((), Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(st)((acc, x) => onModel(body, model, acc, env + (b -> x))._2))
    case Steps.Collect(xs, b, body) =>
      val (ys, st1) = Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Vector.empty[Any], st)) { case ((ys, si), x) =>
        val (y, sj) = onModel(body, model, si, env + (b -> x)); (ys :+ y, sj)
      }
      (ys.toList, st1)
    case Steps.Accumulate(xs, z, acc, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Eval.compile(z)(env), st)) { case ((a, si), x) =>
        onModel(body, model, si, env + (acc -> a) + (b -> x))
      }
    case Steps.Branch(c, a, b)     =>
      val holds = Eval.compile(c)(env).asInstanceOf[Boolean]
      Watch.hit(c, if holds then 1 else 2)
      if holds then onModel(a, model, st, env) else onModel(b, model, st, env)
    case other                     => throw IllegalStateException(s"FrFlow: a model calls no boundary ($other)")

  /** A value handed to an implementation of a boundary, as the term its operation takes. */
  def literal(v: Any): Term[Any] = Term(Tree.Lit(v, LeanType.unknown), LeanType.unknown)

  /** The flow now, on the given implementations: how a production implementation is checked against its model. */
  def runNow(s: Steps, env: Env, impls: Map[Boundary[?], Any]): Any = s match
    case Steps.Ret(t)            => Eval.compile(t)(env)
    case Steps.Op(b, m, args)    =>
      val vs = args.map(a => literal(Eval.compile(a)(env)))
      def call = runNow(Steps.of(m.invoke(impls(b), vs*).asInstanceOf[Flow[?]])._1, Map.empty, impls)
      b.failure.fold(call)(e => try call catch case x: Exception if !x.isInstanceOf[FlowFailed] => throw FlowFailed(Eval.compile(e.termTree)(Map.empty)))
    case Steps.Seq(a, b, rest)   => runNow(rest, env + (b -> runNow(a, env, impls)), impls)
    case Steps.Let(b, v, rest)   => runNow(rest, env + (b -> Eval.compile(v)(env)), impls)
    case Steps.Loop(xs, b, body) => Eval.compile(xs)(env).asInstanceOf[List[Any]].foreach(x => runNow(body, env + (b -> x), impls))
    case Steps.Collect(xs, b, body) => Eval.compile(xs)(env).asInstanceOf[List[Any]].map(x => runNow(body, env + (b -> x), impls))
    case Steps.Accumulate(xs, z, acc, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(Eval.compile(z)(env))((a, x) => runNow(body, env + (acc -> a) + (b -> x), impls))
    case Steps.Branch(c, a, b)   => if Eval.compile(c)(env).asInstanceOf[Boolean] then runNow(a, env, impls) else runNow(b, env, impls)
    case Steps.Raise(e, _)       => throw FlowFailed(Eval.compile(e)(env))
    case Steps.Catch(body, t, b, handler) =>
      try runNow(body, env, impls)
      catch case FlowFailed(err) if handles(t, err) => runNow(handler, env + (b -> err), impls)
    case Steps.Outside(run)      => run()
    // Now, one step at a time: a race's left side wins.
    case Steps.Race(l, _, _)     => Left(runNow(l, env, impls))
    case other if Steps.reading(other).isDefined => runNow(Steps.sequential(other), env, impls)
    case other                   => throw IllegalStateException(s"FrFlow: production runs no model's step ($other)")

  /** The flow in `F`, its calls going to the bound implementations; a term is evaluated under `bindings`. In a
    * concurrent `F` (`GenConcurrent`: cats-effect's `IO`), branches run at once on fibers, a race cancels its loser and
    * a transaction holds its boundaries' locks; in another (`SyncIO`) they run in turn, as the proofs read them.
    * `beforeCall` runs before each call of a boundary: where a test lets the scheduler interleave the branches.
    */
  def run[F[_]](s: Steps, env: Env, impls: Map[Boundary[?], Any], bindings: Seq[Binding], beforeCall: Option[F[Unit]] = None)(
      using F: cats.effect.kernel.Sync[F]): F[Any] =
    import cats.syntax.all.*
    import cats.effect.kernel.syntax.all.*
    val conc: Option[cats.effect.kernel.GenConcurrent[F, Throwable]] = F match
      case c: cats.effect.kernel.GenConcurrent[F, Throwable] @unchecked => Some(c)
      case _                                                           => None
    val bound = Bindings.prepare(bindings)
    def eval(t: Tree, env: Env): F[Any] = F.delay(Bindings.within(bound)(Eval.compile(t)(env)))
    def go(s: Steps, env: Env): F[Any] = s match
      case Steps.Ret(t)            => eval(t, env)
      case Steps.Op(b, m, args)    =>
        val impl = impls.getOrElse(b, throw IllegalStateException(s"FrFlow: bind the boundary ${b.name} (${b.name}.bind(…))"))
        val call = args.traverse(eval(_, env)).flatMap { vs =>
          (impl, F) match
            // The computer's clock on fibers: a sleep that blocks no thread, and is cancelled when its fiber is.
            case (SystemClock, t: cats.effect.kernel.GenTemporal[F, Throwable] @unchecked) if m.getName == "sleep" =>
              val s = vs.head match { case b: BigInt => b; case i: Int => BigInt(i); case l: Long => BigInt(l); case _ => BigInt(0) }
              t.sleep(scala.concurrent.duration.FiniteDuration(s.max(0).toLong, java.util.concurrent.TimeUnit.SECONDS)).widen
            case _ =>
              F.delay(m.invoke(impl, vs.map(literal)*).asInstanceOf[Flow[?]]).flatMap(f => go(Steps.of(f)._1, Map.empty))
        }
        // A failing boundary's exception is its error, as the proofs see it.
        val failing = b.failure.fold(call)(e => call.adaptError { case x: Exception if !x.isInstanceOf[FlowFailed] => FlowFailed(Eval.compile(e.termTree)(Map.empty)) })
        beforeCall.fold(failing)(_ *> failing)
      case Steps.Raise(e, _)       => eval(e, env).flatMap(v => F.raiseError(FlowFailed(v)))
      case Steps.Catch(body, t, b, handler) =>
        go(body, env).handleErrorWith {
          case FlowFailed(err) if handles(t, err) => go(handler, env + (b -> err))
          case other                          => F.raiseError(other)
        }
      case Steps.Seq(a, b, rest)   => go(a, env).flatMap(x => go(rest, env + (b -> x)))
      case Steps.Let(b, v, rest)   => eval(v, env).flatMap(x => go(rest, env + (b -> x)))
      case Steps.Loop(xs, b, body) => eval(xs, env).flatMap(v => v.asInstanceOf[List[Any]].traverse_(x => go(body, env + (b -> x)))).as(())
      case Steps.Collect(xs, b, body) => eval(xs, env).flatMap(v => v.asInstanceOf[List[Any]].traverse(x => go(body, env + (b -> x)))).widen
      case Steps.Accumulate(xs, z, acc, b, body) =>
        (eval(xs, env), eval(z, env)).tupled.flatMap((v, z0) => v.asInstanceOf[List[Any]].foldM(z0)((a, x) => go(body, env + (acc -> a) + (b -> x))))
      case Steps.Branch(c, a, b)   => eval(c, env).flatMap(v => if v.asInstanceOf[Boolean] then go(a, env) else go(b, env))
      case Steps.Outside(run)      => F.delay(run())
      case Steps.Par(l, _, r, _) => conc.fold(go(Steps.sequential(s), env))(c => c.both(go(l, env), go(r, env)).widen)
      case Steps.ParEach(xs, b, body, limit, _) => eval(xs, env).flatMap { v =>
          val ys = v.asInstanceOf[List[Any]]
          conc.fold(ys.traverse(x => go(body, env + (b -> x))))(c => c.parTraverseN(limit.getOrElse(ys.size).max(1))(ys)(x => go(body, env + (b -> x)))).widen
        }
      case Steps.Atomic(body)      => Transactions.atomically(Steps.boundaries(body))(go(body, env))
      case Steps.Race(l, r, _)     => conc.fold(go(l, env).map(Left(_)))(c => c.race(go(l, env), go(r, env))).widen
      // The finalizer after a result, and after an error of `t` (raised again); and when the body is cancelled.
      case Steps.Guard(body, t, fin, _) =>
        F.uncancelable(poll => poll(go(body, env)).onCancel(go(fin, env).void).attempt.flatMap {
          case Right(a)                                => go(fin, env).as(a)
          case Left(FlowFailed(err)) if handles(t, err) => go(fin, env) *> F.raiseError(FlowFailed(err))
          case Left(other)                             => F.raiseError(other)
        })
      case other                   => F.raiseError(IllegalStateException(s"FrFlow: production runs no model's step ($other)"))
    go(s, env)
