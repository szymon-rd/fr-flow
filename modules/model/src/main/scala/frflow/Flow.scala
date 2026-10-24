package frflow

import java.lang.reflect.{InvocationHandler, Method, ParameterizedType, Proxy, Type}
import scala.reflect.ClassTag

/** Steps over boundaries (a database, a clock, an event log), written as Cats or ZIO code is: `for s <- db.load …
  * yield t`. A flow is built once, on symbolic values: Lean reads it as a `do` block over any monad with the
  * boundaries' operations, and Scala compiles it to run in any `cats.effect.Sync`.
  */
sealed abstract class Flow[A]:
  def flatMap[B](f: Term[A] => Flow[B]): Flow[B] = Flow.Bind(this, f, f)
  def map[B](f: Term[A] => Term[B]): Flow[B] = Flow.Bind(this, (a: Term[A]) => Flow.Pure(f(a)), f)

object Flow:
  private[frflow] final case class Pure[A](t: Term[A]) extends Flow[A]
  private[frflow] final case class Call[A](boundary: Boundary[?], method: Method, args: List[Term[?]]) extends Flow[A]
  /** `named`: the lambda the program wrote, which names the value bound. */
  private[frflow] final case class Bind[X, A](first: Flow[X], next: Term[X] => Flow[A], named: AnyRef) extends Flow[A]
  private[frflow] final case class Each[X](xs: Term[List[X]], body: Term[X] => Flow[?]) extends Flow[Unit]
  private[frflow] final case class Cond[A](c: Term[Boolean], a: Flow[A], b: Flow[A]) extends Flow[A]
  private[frflow] final case class Get[S](model: StateModel[S]) extends Flow[S]
  private[frflow] final case class Put[S](model: StateModel[S], s: Term[S]) extends Flow[Unit]
  private[frflow] final case class Update[S](model: StateModel[S], f: Term[S] => Term[S]) extends Flow[Unit]
  private[frflow] final case class Effect[A](run: () => A) extends Flow[A]

  def pure[A](t: Term[A]): Flow[A] = Pure(t)
  val unit: Flow[Unit] = Pure(Term.lit(()))
  /** A step of the outside world, for a production implementation of a boundary: proven code never takes one. */
  def effect[A](a: => A): Flow[A] = Effect(() => a)
  /** The same, on the values of the terms an operation was called with: `Flow.effect(id, t)(sql.storeAbout)`. */
  def effect[X, A](x: Term[X])(f: X => A): Flow[A] = Effect(() => f(valueOf(x)))
  def effect[X, Y, A](x: Term[X], y: Term[Y])(f: (X, Y) => A): Flow[A] = Effect(() => f(valueOf(x), valueOf(y)))
  def effect[X, Y, Z, A](x: Term[X], y: Term[Y], z: Term[Z])(f: (X, Y, Z) => A): Flow[A] = Effect(() => f(valueOf(x), valueOf(y), valueOf(z)))
  private def valueOf[X](t: Term[X]): X = Eval.compile(t.termTree)(Map.empty).asInstanceOf[X]
  /** `Flow.when(c)(step)`: the step if `c` holds. */
  def when(c: Term[Boolean])(step: Flow[?]): Flow[Unit] = Cond(c, step.map(_ => Term.lit(())), unit)

final class ThenFlow[R](c: Term[Boolean], a: Flow[R]):
  def Else(b: Flow[R]): Flow[R] = Flow.Cond(c, a, b)

/** What proven code calls but cannot see: a plain trait of operations taking terms and returning flows. The
  * model names one value for it, as `Param` does for a term; production binds an implementation of the trait.
  * `db.load` calls the operation (an implicit conversion to the trait).
  */
final class Boundary[T] private (val name: String, val means: String, val cls: Class[T]):
  /** The trait, recording each call as a step. */
  lazy val ops: T = Proxy.newProxyInstance(cls.getClassLoader, Array(cls), new InvocationHandler:
    def invoke(p: AnyRef, m: Method, args: Array[AnyRef] | Null): AnyRef =
      m.getName match
        case "toString" if m.getParameterCount == 0 => s"Boundary($name)"
        case "hashCode" if m.getParameterCount == 0 => Integer.valueOf(System.identityHashCode(p))
        case "equals" if m.getParameterCount == 1   => java.lang.Boolean.valueOf(p eq args.nn(0))
        case _ => Flow.Call[Any](Boundary.this, m, Option(args).fold(Nil)(_.toList.map(_.asInstanceOf[Term[?]])))
  ).asInstanceOf[T]
  /** The production implementation. */
  def bind(impl: T): Boundary.Bound = Boundary.Bound(this, impl)
  /** The operations, in the trait's order: what Lean's class declares. */
  private[frflow] def operations: List[Method] =
    cls.getMethods.toList.filter(m => classOf[Flow[?]].isAssignableFrom(m.getReturnType)).sortBy(_.getName)
  /** Lean's name of the class. */
  def lean: String = Names.ident(cls.getSimpleName)
  override def toString: String = name

object Boundary:
  def apply[T](name: String, means: String)(using ct: ClassTag[T]): Boundary[T] =
    val c = ct.runtimeClass.asInstanceOf[Class[T]]
    require(c.isInterface, s"FrFlow: the boundary $name is a trait of operations, not ${c.getName}")
    new Boundary(name, means, c)
  given ops[T]: Conversion[Boundary[T], T] = _.ops
  final case class Bound(boundary: Boundary[?], impl: Any)

/** What a boundary does, as the proofs see it: an implementation of its trait over a state `S`, read and changed
  * with `state.get`, `state.set` and `state.update`. Deterministic, never failing, with the boundary to itself
  * during a run: what is unknown (a clock's readings) goes into the state.
  */
trait StateModel[S](using private[frflow] val stateType: LeanType[S]):
  protected final val state: State[S] = State(this)
  /** Lean's namespace of the model's operations. */
  private[frflow] def lean: String = Names.ident(getClass.getSimpleName.stripSuffix("$"))
  /** The boundary's trait this models: the one interface of the model's whose methods are flows. */
  private[frflow] lazy val boundaryTrait: Class[?] =
    getClass.getInterfaces.find(i => i.getMethods.exists(m => classOf[Flow[?]].isAssignableFrom(m.getReturnType)))
      .getOrElse(throw IllegalStateException(s"FrFlow: $lean implements no boundary (a trait of operations returning flows)"))
  /** Its field in Lean's `World`: the trait's name, lowered (`database`). */
  private[frflow] def field: String = Names.ident(boundaryTrait.getSimpleName.head.toLower.toString + boundaryTrait.getSimpleName.tail)

final class State[S] private[frflow] (model: StateModel[S]):
  def get: Flow[S] = Flow.Get(model)
  def set(s: Term[S]): Flow[Unit] = Flow.Put(model, s)
  def update(f: Term[S] => Term[S]): Flow[Unit] = Flow.Update(model, f)

/** The states of the boundaries' models, before or after a flow runs: `before(DatabaseModel)`. */
final class World private[frflow] (private[frflow] val parts: Map[StateModel[?], Any]):
  def apply[S](m: StateModel[S]): S = parts(m).asInstanceOf[S]
  private[frflow] def updated(m: StateModel[?], s: Any): World = new World(parts.updated(m, s))
  override def equals(o: Any): Boolean = o match { case w: World => w.parts == parts; case _ => false }
  override def hashCode: Int = parts.hashCode
  override def toString: String = parts.map((m, s) => s"${m.lean} = ${Example.show(s)}").mkString("World(", ", ", ")")

object World:
  def apply(parts: (StateModel[?], Any)*): World = new World(parts.toMap)
  given LeanType[World] = LeanType.of(Shape.WorldT)
  extension (w: Term[World])
    def apply[S](m: StateModel[S]): Term[S] = Term(Tree.Part(w.termTree, m), m.stateType)

/** A flow built once on symbolic values: what Lean prints and Scala runs. */
private[frflow] enum Steps:
  case Ret(t: Tree)
  case Op(boundary: Boundary[?], method: Method, args: List[Tree])
  /** `let b ← first; rest` (`b` unused when a wildcard). */
  case Seq(first: Steps, b: Binder, rest: Steps)
  case Loop(xs: Tree, b: Binder, body: Steps)
  case Branch(c: Tree, a: Steps, b: Steps)
  case Read(model: StateModel[?])
  case Write(model: StateModel[?], s: Tree)
  case Modify(model: StateModel[?], b: Binder, body: Tree)
  case Outside(run: () => Any)
  /** `let b := v; rest`: a value the program named (`t = …` in a for-comprehension), computed once. */
  case Let(b: Binder, v: Tree, rest: Steps)

private[frflow] object Steps:
  /** The steps of a flow, and the type of its result. */
  def of(f: Flow[?]): (Steps, LeanType[?]) = within(f, Nil)

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
      case Flow.Cond(_, a, b)         => shared(a) ++ shared(b)
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
    case Flow.Cond(c, a, b)    => val (sa, t) = within(a, bound); (Branch(c.termTree, sa, within(b, bound)._1), t)
    case Flow.Get(m)           => (Read(m), m.stateType)
    case Flow.Put(m, s)        => (Write(m, s.termTree), summon[LeanType[Unit]])
    case Flow.Update(m, f)     =>
      val b = Lambda.binders(f, List(m.stateType)).head
      (Modify(m, b, f.asInstanceOf[Term[Any] => Term[Any]](b.term).termTree), summon[LeanType[Unit]])
    case Flow.Effect(run)      => (Outside(run), LeanType.unknown)

  def fold[A](s: Steps, z: A)(f: (A, Steps) => A): A =
    val here = f(z, s)
    s match
      case Seq(a, _, b)    => fold(b, fold(a, here)(f))(f)
      case Loop(_, _, b)   => fold(b, here)(f)
      case Branch(_, a, b) => fold(b, fold(a, here)(f))(f)
      case Let(_, _, r)    => fold(r, here)(f)
      case _               => here

  def boundaries(s: Steps): List[Boundary[?]] = fold(s, List.empty[Boundary[?]]) {
    case (acc, Op(b, _, _)) if !acc.contains(b) => acc :+ b
    case (acc, _)                               => acc
  }
  def effectful(s: Steps): Boolean = fold(s, false)((acc, x) => acc || x.isInstanceOf[Outside])

/** A program attached to a contract as its proven code: a `def` from its input to a flow. */
final class FlowDef[A, R] @scala.annotation.publicInBinary private[frflow] (val name: String, f: Term[A] => Flow[R],
    inType: LeanType[A], val source: String):
  private[frflow] lazy val built: (Binder, Steps, LeanType[?]) =
    Building {
      val b = Lambda.binders(f, List(inType)).head
      val (s, t) = Steps.of(f(b.term))
      (b, s, t)
    }

/** Running flows: on the models (the proofs' world, held in Scala), and in production (any `Sync`). */
private[frflow] object Flows:
  import Eval.Env

  /** The flow on the models: its result and the world after. A call goes to the model of its boundary. */
  def onModels(s: Steps, env: Env, w: World): (Any, World) = s match
    case Steps.Ret(t)            => (Eval.compile(t)(env), w)
    case Steps.Op(b, m, args)    =>
      val model = w.parts.keys.find(x => b.cls.isInstance(x))
        .getOrElse(throw IllegalStateException(s"FrFlow: no model of the boundary ${b.name} in $w"))
      val inner = Steps.of(m.invoke(model, args.map(a => literal(Eval.compile(a)(env)))*).asInstanceOf[Flow[?]])._1
      val (r, own) = onModel(inner, model, w(model.asInstanceOf[StateModel[Any]]))
      (r, w.updated(model, own))
    case Steps.Seq(a, b, rest)   => val (x, w1) = onModels(a, env, w); onModels(rest, env + (b -> x), w1)
    case Steps.Let(b, v, rest)   => onModels(rest, env + (b -> Eval.compile(v)(env)), w)
    case Steps.Loop(xs, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(((): Any, w))((acc, x) => (((), onModels(body, env + (b -> x), acc._2)._2)))
    case Steps.Branch(c, a, b)   => if Eval.compile(c)(env).asInstanceOf[Boolean] then onModels(a, env, w) else onModels(b, env, w)
    case other                   => throw IllegalStateException(s"FrFlow: a proven flow takes no step of a model's own ($other)")

  /** A model's own operation, on its state. */
  private def onModel(s: Steps, model: StateModel[?], st: Any, env: Env = Map.empty): (Any, Any) = s match
    case Steps.Ret(t)              => (Eval.compile(t)(env), st)
    case Steps.Read(_)             => (st, st)
    case Steps.Write(_, t)         => ((), Eval.compile(t)(env))
    case Steps.Modify(_, b, body)  => ((), Eval.compile(body)(env + (b -> st)))
    case Steps.Seq(a, b, rest)     => val (x, st1) = onModel(a, model, st, env); onModel(rest, model, st1, env + (b -> x))
    case Steps.Let(b, v, rest)     => onModel(rest, model, st, env + (b -> Eval.compile(v)(env)))
    case Steps.Loop(xs, b, body)   =>
      ((), Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(st)((acc, x) => onModel(body, model, acc, env + (b -> x))._2))
    case Steps.Branch(c, a, b)     => if Eval.compile(c)(env).asInstanceOf[Boolean] then onModel(a, model, st, env) else onModel(b, model, st, env)
    case other                     => throw IllegalStateException(s"FrFlow: a model calls no boundary ($other)")

  /** A value handed to an implementation of a boundary, as the term its operation takes. */
  def literal(v: Any): Term[Any] = Term(Tree.Lit(v, LeanType.unknown), LeanType.unknown)

  /** The flow now, on the given implementations: how a production implementation is checked against its model. */
  def runNow(s: Steps, env: Env, impls: Map[Boundary[?], Any]): Any = s match
    case Steps.Ret(t)            => Eval.compile(t)(env)
    case Steps.Op(b, m, args)    =>
      val f = m.invoke(impls(b), args.map(a => literal(Eval.compile(a)(env)))*).asInstanceOf[Flow[?]]
      runNow(Steps.of(f)._1, Map.empty, impls)
    case Steps.Seq(a, b, rest)   => runNow(rest, env + (b -> runNow(a, env, impls)), impls)
    case Steps.Let(b, v, rest)   => runNow(rest, env + (b -> Eval.compile(v)(env)), impls)
    case Steps.Loop(xs, b, body) => Eval.compile(xs)(env).asInstanceOf[List[Any]].foreach(x => runNow(body, env + (b -> x), impls))
    case Steps.Branch(c, a, b)   => if Eval.compile(c)(env).asInstanceOf[Boolean] then runNow(a, env, impls) else runNow(b, env, impls)
    case Steps.Outside(run)      => run()
    case other                   => throw IllegalStateException(s"FrFlow: production runs no model's step ($other)")

  /** The flow in `F`, its calls going to the bound implementations; a term is evaluated under `bindings`. */
  def run[F[_]](s: Steps, env: Env, impls: Map[Boundary[?], Any], bindings: Seq[Binding])(using F: cats.effect.kernel.Sync[F]): F[Any] =
    import cats.syntax.all.*
    def eval(t: Tree, env: Env): F[Any] = F.delay(Bindings.within(bindings)(Eval.compile(t)(env)))
    def go(s: Steps, env: Env): F[Any] = s match
      case Steps.Ret(t)            => eval(t, env)
      case Steps.Op(b, m, args)    =>
        val impl = impls.getOrElse(b, throw IllegalStateException(s"FrFlow: bind the boundary ${b.name} (${b.name}.bind(…))"))
        args.traverse(eval(_, env)).flatMap { vs =>
          F.delay(m.invoke(impl, vs.map(literal)*).asInstanceOf[Flow[?]]).flatMap(f => go(Steps.of(f)._1, Map.empty))
        }
      case Steps.Seq(a, b, rest)   => go(a, env).flatMap(x => go(rest, env + (b -> x)))
      case Steps.Let(b, v, rest)   => eval(v, env).flatMap(x => go(rest, env + (b -> x)))
      case Steps.Loop(xs, b, body) => eval(xs, env).flatMap(v => v.asInstanceOf[List[Any]].traverse_(x => go(body, env + (b -> x)))).as(())
      case Steps.Branch(c, a, b)   => eval(c, env).flatMap(v => if v.asInstanceOf[Boolean] then go(a, env) else go(b, env))
      case Steps.Outside(run)      => F.delay(run())
      case other                   => F.raiseError(IllegalStateException(s"FrFlow: production runs no model's step ($other)"))
    go(s, env)

/** Trees by identity: a named value's tree is the one object at each of its uses. */
private[frflow] object Trees:
  private def children(t: Tree): List[Tree] = t match
    case Tree.Var(_) | Tree.Lit(_, _) | Tree.Ref(_) => Nil
    case Tree.Call(_, as)          => as
    case Tree.Apply(f, as)         => f :: as
    case Tree.Fun(_, b)            => List(b)
    case Tree.Quant(_, _, b)       => List(b)
    case Tree.If(c, a, b)          => List(c, a, b)
    case Tree.Match(on, cs)        => on :: cs.map(_.body)
    case Tree.Let(_, v, b)         => List(v, b)
    case Tree.Field(on, _, _)      => List(on)
    case Tree.Copy(on, _, us)      => on :: us.map(_._2)
    case Tree.Make(_, _, as)       => as
    case Tree.Tup(es)              => es
    case Tree.Proj(on, _, _)       => List(on)
    case Tree.SomeT(a)             => List(a)
    case Tree.ListT(es)            => es
    case Tree.Over(_, on, _, b)    => List(on, b)
    case Tree.Op(_, as)            => as
    case Tree.Do(s)                => trees(s)
    case Tree.RunOn(c, w)          => List(c, w)
    case Tree.Part(w, _)           => List(w)

  private def trees(s: Steps): List[Tree] = Steps.fold(s, List.empty[Tree]) {
    case (acc, Steps.Ret(t))          => acc :+ t
    case (acc, Steps.Op(_, _, as))    => acc ++ as
    case (acc, Steps.Loop(xs, _, _))  => acc :+ xs
    case (acc, Steps.Branch(c, _, _)) => acc :+ c
    case (acc, Steps.Write(_, t))     => acc :+ t
    case (acc, Steps.Modify(_, _, t)) => acc :+ t
    case (acc, Steps.Let(_, v, _))    => acc :+ v
    case (acc, _)                     => acc
  }

  def occurs(x: Tree, in: Tree): Boolean = (in eq x) || children(in).exists(occurs(x, _))
  def occurs(x: Tree, in: Steps): Boolean = trees(in).exists(occurs(x, _))

  /** `in` with `x` (that object) replaced by `by`. */
  def replace(in: Tree, x: Tree, by: Tree): Tree =
    def go(t: Tree): Tree = if t eq x then by else t match
      case Tree.Var(_) | Tree.Lit(_, _) | Tree.Ref(_) => t
      case Tree.Call(d, as)          => Tree.Call(d, as.map(go))
      case Tree.Apply(f, as)         => Tree.Apply(go(f), as.map(go))
      case Tree.Fun(bs, b)           => Tree.Fun(bs, go(b))
      case Tree.Quant(a, bs, b)      => Tree.Quant(a, bs, go(b))
      case Tree.If(c, a, b)          => Tree.If(go(c), go(a), go(b))
      case Tree.Match(on, cs)        => Tree.Match(go(on), cs.map(c => c.copy(body = go(c.body))))
      case Tree.Let(b, v, body)      => Tree.Let(b, go(v), go(body))
      case Tree.Field(on, a, i)      => Tree.Field(go(on), a, i)
      case Tree.Copy(on, a, us)      => Tree.Copy(go(on), a, us.map((i, v) => (i, go(v))))
      case Tree.Make(a, c, as)       => Tree.Make(a, c, as.map(go))
      case Tree.Tup(es)              => Tree.Tup(es.map(go))
      case Tree.Proj(on, i, n)       => Tree.Proj(go(on), i, n)
      case Tree.SomeT(a)             => Tree.SomeT(go(a))
      case Tree.ListT(es)            => Tree.ListT(es.map(go))
      case Tree.Over(k, on, b, body) => Tree.Over(k, go(on), b, go(body))
      case Tree.Op(op, as)           => Tree.Op(op, as.map(go))
      case Tree.Do(s)                => Tree.Do(replaceIn(s, x, by))
      case Tree.RunOn(c, w)          => Tree.RunOn(go(c), go(w))
      case Tree.Part(w, m)           => Tree.Part(go(w), m)
    go(in)

  def replaceIn(s: Steps, x: Tree, by: Tree): Steps =
    def t(a: Tree) = replace(a, x, by)
    def go(s: Steps): Steps = s match
      case Steps.Ret(a)              => Steps.Ret(t(a))
      case Steps.Op(b, m, as)        => Steps.Op(b, m, as.map(t))
      case Steps.Seq(a, b, rest)     => Steps.Seq(go(a), b, go(rest))
      case Steps.Loop(xs, b, body)   => Steps.Loop(t(xs), b, go(body))
      case Steps.Branch(c, a, b)     => Steps.Branch(t(c), go(a), go(b))
      case Steps.Write(m, a)         => Steps.Write(m, t(a))
      case Steps.Modify(m, b, body)  => Steps.Modify(m, b, t(body))
      case Steps.Let(b, v, rest)     => Steps.Let(b, t(v), go(rest))
      case other                     => other
    go(s)
