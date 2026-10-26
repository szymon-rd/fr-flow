package frflow

/** Trees by identity: a named value's tree is the same object at each of its uses. */
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
    case Tree.Inj(_, a)            => List(a)
    case Tree.ListT(es)            => es
    case Tree.Over(_, on, _, b)    => List(on, b)
    case Tree.Op(_, as)            => as
    case Tree.Do(s)                => trees(s)
    case Tree.RunOn(c, w, _)       => List(c, w)
    case Tree.Part(w, _)           => List(w)

  private[frflow] def trees(s: Steps): List[Tree] = Steps.fold(s, List.empty[Tree]) {
    case (acc, Steps.Ret(t))          => acc :+ t
    case (acc, Steps.Op(_, _, as))    => acc ++ as
    case (acc, Steps.Loop(xs, _, _))  => acc :+ xs
    case (acc, Steps.Collect(xs, _, _)) => acc :+ xs
    case (acc, Steps.Accumulate(xs, z, _, _, _)) => acc :+ xs :+ z
    case (acc, Steps.Branch(c, _, _)) => acc :+ c
    case (acc, Steps.Write(_, t))     => acc :+ t
    case (acc, Steps.Modify(_, _, t)) => acc :+ t
    case (acc, Steps.Let(_, v, _))    => acc :+ v
    case (acc, Steps.Raise(e, _))     => acc :+ e
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
      case Tree.Inj(l, a)            => Tree.Inj(l, go(a))
      case Tree.ListT(es)            => Tree.ListT(es.map(go))
      case Tree.Over(k, on, b, body) => Tree.Over(k, go(on), b, go(body))
      case Tree.Op(op, as)           => Tree.Op(op, as.map(go))
      case Tree.Do(s)                => Tree.Do(replaceIn(s, x, by))
      case Tree.RunOn(c, w, e)       => Tree.RunOn(go(c), go(w), e)
      case Tree.Part(w, m)           => Tree.Part(go(w), m)
    go(in)

  def replaceIn(s: Steps, x: Tree, by: Tree): Steps =
    def t(a: Tree) = replace(a, x, by)
    def go(s: Steps): Steps = s match
      case Steps.Ret(a)              => Steps.Ret(t(a))
      case Steps.Op(b, m, as)        => Steps.Op(b, m, as.map(t))
      case Steps.Seq(a, b, rest)     => Steps.Seq(go(a), b, go(rest))
      case Steps.Loop(xs, b, body)   => Steps.Loop(t(xs), b, go(body))
      case Steps.Collect(xs, b, body) => Steps.Collect(t(xs), b, go(body))
      case Steps.Accumulate(xs, z, acc, b, body) => Steps.Accumulate(t(xs), t(z), acc, b, go(body))
      case Steps.Branch(c, a, b)     => Steps.Branch(t(c), go(a), go(b))
      case Steps.Write(m, a)         => Steps.Write(m, t(a))
      case Steps.Modify(m, b, body)  => Steps.Modify(m, b, t(body))
      case Steps.Let(b, v, rest)     => Steps.Let(b, t(v), go(rest))
      case Steps.Raise(e, err)       => Steps.Raise(t(e), err)
      case Steps.Catch(a, err, b, h) => Steps.Catch(go(a), err, b, go(h))
      case Steps.Par(l, a, r, b)     => Steps.Par(go(l), a, go(r), b)
      case Steps.ParEach(xs, b, body, n, o) => Steps.ParEach(t(xs), b, go(body), n, o)
      case Steps.Atomic(body)        => Steps.Atomic(go(body))
      case Steps.Race(l, r, reading) => Steps.Race(go(l), go(r), go(reading))
      case Steps.Guard(body, err, fin, reading) => Steps.Guard(go(body), err, go(fin), go(reading))
      case other                     => other
    go(s)
