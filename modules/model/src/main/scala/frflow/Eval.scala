package frflow

/** A term's tree compiled once into Scala: what the runtime, the examples and the probes call. Parameters are read
  * from the values in force (`Bindings`) on each call; `forall` and `exists` cannot run.
  */
private[frflow] object Eval:
  type Env = Map[Binder, Any]
  type Run = Env => Any

  /** The Scala function of `bs` (of arity 0 to 5) that `body` computes. */
  def function(bs: List[Binder], body: Tree): AnyRef = closure(bs, compile(body), Map.empty)

  private def closure(bs: List[Binder], run: Run, env: Env): AnyRef = bs match
    case Nil                   => () => run(env)
    case List(a)               => (x: Any) => run(env + (a -> x))
    case List(a, b)            => (x: Any, y: Any) => run(env + (a -> x) + (b -> y))
    case List(a, b, c)         => (x: Any, y: Any, z: Any) => run(env + (a -> x) + (b -> y) + (c -> z))
    case List(a, b, c, d)      => (x: Any, y: Any, z: Any, w: Any) => run(env + (a -> x) + (b -> y) + (c -> z) + (d -> w))
    case List(a, b, c, d, e)   => (x: Any, y: Any, z: Any, w: Any, v: Any) => run(env + (a -> x) + (b -> y) + (c -> z) + (d -> w) + (e -> v))
    case _                     => throw IllegalArgumentException("FrFlow: at most five parameters")

  def call(f: Any, args: List[Any]): Any = (f, args) match
    case (g: Function0[?], Nil)                                  => g()
    case (g: Function1[Any, ?] @unchecked, List(a))              => g(a)
    case (g: Function2[Any, Any, ?] @unchecked, List(a, b))      => g(a, b)
    case (g: Function3[Any, Any, Any, ?] @unchecked, List(a, b, c)) => g(a, b, c)
    case (g: Function4[Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d)) => g(a, b, c, d)
    case (g: Function5[Any, Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d, e)) => g(a, b, c, d, e)
    case _ => throw IllegalArgumentException(s"FrFlow: cannot call $f on ${args.size} arguments")

  private def num(v: Any): BigInt = v match
    case i: Int    => BigInt(i)
    case l: Long   => BigInt(l)
    case b: BigInt => b
    case o         => throw IllegalArgumentException(s"FrFlow: $o is not a number")
  private def bool(v: Any): Boolean = v.asInstanceOf[Boolean]
  private def list(v: Any): List[Any] = v.asInstanceOf[List[Any]]
  private def map(v: Any): Map[Any, Any] = v.asInstanceOf[Map[Any, Any]]
  private def set(v: Any): Set[Any] = v.asInstanceOf[Set[Any]]
  private def fields(v: Any): List[Any] = v.asInstanceOf[Product].productIterator.toList
  /** A result of the same Scala type as the operands' (an Int stays an Int). */
  private def like(a: Any, n: BigInt): Any = a match
    case _: Int  => n.toInt
    case _: Long => n.toLong
    case _       => n

  def compile(t: Tree): Run = t match
    case Tree.Var(b)          => env => env(b)
    case Tree.Lit(v, _)       => _ => v
    case Tree.Ref(p)          => _ => Bindings.get(p)
    case Tree.Call(d, args)   =>
      val as = args.map(compile)
      env => call(d.fn, as.map(_(env)))
    case Tree.Apply(f, args)  =>
      val (cf, as) = (compile(f), args.map(compile))
      env => call(cf(env), as.map(_(env)))
    case Tree.Fun(bs, body)   =>
      val run = compile(body)
      env => closure(bs, run, env)
    case Tree.Quant(all, _, _) => _ => throw NotExecutable(if all then "forall" else "exists")
    case Tree.If(c, a, b)     =>
      val (rc, ra, rb) = (compile(c), compile(a), compile(b))
      env => if bool(rc(env)) then ra(env) else rb(env)
    case Tree.Match(on, cases) =>
      val ro = compile(on)
      val rs = cases.map(c => (c.pat, compile(c.body)))
      env =>
        val v = ro(env)
        rs.iterator.map((pat, run) => matches(pat, v).map(bound => run(env ++ bound))).collectFirst { case Some(r) => r }
          .getOrElse(throw MatchError(v))
    case Tree.Let(b, v, body) =>
      val (rv, rb) = (compile(v), compile(body))
      env => rb(env + (b -> rv(env)))
    case Tree.Field(on, _, i) =>
      val r = compile(on)
      env => r(env).asInstanceOf[Product].productElement(i)
    case Tree.Copy(on, adt, ups) =>
      val r = compile(on)
      val us = ups.map((i, u) => i -> compile(u))
      env =>
        val fs = fields(r(env)).toArray
        us.foreach((i, u) => fs(i) = u(env))
        adt.ctors.head.make(fs.toList)
    case Tree.Make(_, c, args) =>
      val as = args.map(compile)
      env => c.make(as.map(_(env)))
    case Tree.Tup(es)         =>
      val rs = es.map(compile)
      env => Tuple.fromArray(rs.map(_(env).asInstanceOf[Object]).toArray)
    case Tree.Proj(on, k, _)  =>
      val r = compile(on)
      env => r(env).asInstanceOf[Product].productElement(k - 1)
    case Tree.SomeT(a)        => val r = compile(a); env => Some(r(env))
    case Tree.ListT(es)       => val rs = es.map(compile); env => rs.map(_(env))
    case Tree.Over(kind, on, b, body) =>
      val (ro, rb) = (compile(on), compile(body))
      env =>
        def p(x: Any) = bool(rb(env + (b -> x)))
        kind match
          case Iter.All       => list(ro(env)).forall(p)
          case Iter.Some      => list(ro(env)).exists(p)
          case Iter.Filter    => list(ro(env)).filter(p)
          case Iter.FilterNot => list(ro(env)).filterNot(p)
          case Iter.Find      => list(ro(env)).find(p)
          case Iter.OptAll    => ro(env).asInstanceOf[Option[Any]].forall(p)
          case Iter.OptSome   => ro(env).asInstanceOf[Option[Any]].exists(p)
    case Tree.Op(op, args)    => prim(op, args.map(compile))
    case Tree.Part(w, m)      => val r = compile(w); env => r(env).asInstanceOf[World](m)
    case Tree.RunOn(Tree.Call(d, args), w) =>
      val (as, rw) = (args.map(compile), compile(w))
      env =>
        val (bs, body) = d.lifted.built
        body.termTree match
          case Tree.Do(steps) => Flows.onModels(steps, bs.zip(as.map(_(env))).toMap, rw(env).asInstanceOf[World])
          case other          => throw IllegalArgumentException(s"FrFlow: ${d.name} is not a flow")
    case Tree.RunOn(other, _) => throw IllegalArgumentException(s"FrFlow: only a flow's call runs on the models, not $other")
    case Tree.Do(_)           => _ => throw IllegalStateException("FrFlow: a flow runs on the models (FrFlow.runOn) or in production (run)")

  private def matches(pat: Pat, v: Any): Option[Env] = pat match
    case Pat.Ctor(adt, c, bs) =>
      Option.when(adt.ctorOf(v) eq c)((if c.fields.isEmpty then Nil else fields(v)).zip(bs).map((x, b) => b -> x).toMap)
    case Pat.SomeP(b)    => v match { case Some(x) => Some(Map(b -> x)); case _ => None }
    case Pat.NoneP       => Option.when(v == None)(Map.empty)
    case Pat.ConsP(h, t) => v match { case x :: rest => Some(Map(h -> x, t -> rest)); case _ => None }
    case Pat.NilP        => Option.when(v == Nil)(Map.empty)

  private def prim(op: Prim, rs: List[Run]): Run =
    def one(f: Any => Any): Run = { val a = rs.head; env => f(a(env)) }
    def two(f: (Any, Any) => Any): Run = { val (a, b) = (rs(0), rs(1)); env => f(a(env), b(env)) }
    def three(f: (Any, Any, Any) => Any): Run = { val (a, b, c) = (rs(0), rs(1), rs(2)); env => f(a(env), b(env), c(env)) }
    op match
      case Prim.Eq         => two(_ == _)
      case Prim.Ne         => two(_ != _)
      case Prim.And        => val (a, b) = (rs(0), rs(1)); env => bool(a(env)) && bool(b(env))
      case Prim.Or         => val (a, b) = (rs(0), rs(1)); env => bool(a(env)) || bool(b(env))
      case Prim.Implies    => val (a, b) = (rs(0), rs(1)); env => !bool(a(env)) || bool(b(env))
      case Prim.Not        => one(a => !bool(a))
      case Prim.Add        => two((a, b) => like(a, num(a) + num(b)))
      case Prim.Sub        => two((a, b) => like(a, num(a) - num(b)))
      case Prim.Mul        => two((a, b) => like(a, num(a) * num(b)))
      // Lean's Int.tdiv and Int.tmod round toward zero, as Scala's do.
      case Prim.Div        => two((a, b) => like(a, num(a) / num(b)))
      case Prim.Mod        => two((a, b) => like(a, num(a) % num(b)))
      case Prim.Lt         => two((a, b) => num(a) < num(b))
      case Prim.Le         => two((a, b) => num(a) <= num(b))
      case Prim.Gt         => two((a, b) => num(a) > num(b))
      case Prim.Ge         => two((a, b) => num(a) >= num(b))
      case Prim.Max        => two((a, b) => like(a, num(a).max(num(b))))
      case Prim.Min        => two((a, b) => like(a, num(a).min(num(b))))
      case Prim.Neg        => one(a => like(a, -num(a)))
      case Prim.Concat     => two((a, b) => a.asInstanceOf[String] + b.asInstanceOf[String])
      case Prim.Cons       => two((x, xs) => x :: list(xs))
      case Prim.Append     => two((xs, ys) => list(xs) ++ list(ys))
      case Prim.Contains   => two((xs, x) => list(xs).contains(x))
      case Prim.IsEmpty    => one(xs => list(xs).isEmpty)
      case Prim.NonEmpty   => one(xs => list(xs).nonEmpty)
      case Prim.Length     => one(xs => list(xs).length)
      case Prim.MapL       => two((f, xs) => list(xs).map(x => call(f, List(x))))
      case Prim.FlatMap    => two((f, xs) => list(xs).flatMap(x => list(call(f, List(x)))))
      case Prim.FoldLeft   => three((f, z, xs) => list(xs).foldLeft(z)((acc, x) => call(f, List(acc, x))))
      case Prim.HeadOption => one(xs => list(xs).headOption)
      case Prim.ToSet      => one(xs => list(xs).toSet)
      case Prim.Take       => two((n, xs) => list(xs).take(num(n).toInt))
      case Prim.Drop       => two((n, xs) => list(xs).drop(num(n).toInt))
      case Prim.Zip        => two((xs, ys) => list(xs).zip(list(ys)))
      case Prim.Get        => two((m, k) => map(m).get(k))
      case Prim.HasKey     => two((m, k) => map(m).contains(k))
      case Prim.GetOrElse  => three((m, k, d) => map(m).getOrElse(k, d))
      case Prim.Updated    => three((m, k, v) => map(m).updated(k, v))
      case Prim.Removed    => two((m, k) => map(m).removed(k))
      case Prim.SetHas     => two((s, x) => set(s).contains(x))
      case Prim.Incl       => two((s, x) => set(s) + x)
      case Prim.Excl       => two((s, x) => set(s) - x)
      case Prim.Union      => two((s, x) => set(s) ++ set(x))
      case Prim.Intersect  => two((s, x) => set(s).intersect(set(x)))
      case Prim.SubsetOf   => two((s, x) => set(s).subsetOf(set(x)))
      case Prim.OptContains => two((o, x) => o.asInstanceOf[Option[Any]].contains(x))
      case Prim.IsDefined  => one(o => o.asInstanceOf[Option[Any]].isDefined)
      case Prim.OptIsEmpty => one(o => o.asInstanceOf[Option[Any]].isEmpty)
      case Prim.OptGetOrElse => two((o, d) => o.asInstanceOf[Option[Any]].getOrElse(d))
