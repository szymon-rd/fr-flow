package frflow.proof.lean.laws

import frflow.proof.lean.ast.*

/** `DeBruijn` over what generated Lean binds beside terms: a `do` block's steps (each result bound for the steps
  * after it, a loop's element and a handler's error for their bodies) and a module's declarations (a `def`'s or a
  * theorem's parameters for its type and body, an instance field's for its value): every bound name an index, every
  * binder `_`, so two modules that differ only in how their variables are named read the same.
  */
object DoBlocks:
  import DeBruijn.{blank, under}

  def block(lines: List[DoLine], scope: List[LeanName]): List[DoLine] = lines match
    case Nil          => Nil
    case line :: rest =>
      val (out, after) = step(line, scope)
      out :: block(rest, after)

  private def bound(n: Option[LeanName], scope: List[LeanName]) = n.fold(scope)(_ :: scope)

  private def step(l: DoLine, sc: List[LeanName]): (DoLine, List[LeanName]) = l match
    case DoLine.Bind(n, e)              => (DoLine.Bind(blank, under(e, sc)), n :: sc)
    case DoLine.Let(n, e)               => (DoLine.Let(blank, under(e, sc)), n :: sc)
    case DoLine.Step(e)                 => (DoLine.Step(under(e, sc)), sc)
    case DoLine.BindBlock(n, b)         => (DoLine.BindBlock(n.map(_ => blank), block(b, sc)), bound(n, sc))
    case DoLine.For(x, over, b)         => (DoLine.For(blank, under(over, sc), block(b, x :: sc)), sc)
    case DoLine.Branch(c, a, b)         => (DoLine.Branch(under(c, sc), block(a, sc), block(b, sc)), sc)
    case DoLine.TryCatch(n, e, b, x, h) => (DoLine.TryCatch(n.map(_ => blank), under(e, sc), block(b, sc),
        x.map(_ => blank), block(h, bound(x, sc))), bound(n, sc))
    case DoLine.Traverse(n, head, ps, b) => (DoLine.Traverse(n.map(_ => blank), under(head, sc), ps.map(_ => blank),
        block(b, ps.reverse ++ sc)), bound(n, sc))

  /** A declaration with its variables nameless. */
  def decl(d: Decl): Decl = d match
    case Decl.Documented(doc, x)            => Decl.Documented(doc, decl(x))
    case Decl.Def(as, n, ps, ty, body)      =>
      val (bs, sc) = DeBruijn.binders(ps, Nil)
      Decl.Def(as, n, bs, under(ty, sc), under(body, sc))
    case Decl.Abbrev(as, n, v)              => Decl.Abbrev(as, n, under(v, Nil))
    case Decl.Theorem(as, n, ps, st, p, br) =>
      val (bs, sc) = DeBruijn.binders(ps, Nil)
      Decl.Theorem(as, n, bs, under(st, sc), p match
        case Proof.Below(t) => Proof.Below(under(t, sc))
        case other          => other, br)
    case Decl.Class(n, ps, ops)             =>
      val (bs, sc) = DeBruijn.binders(ps, Nil)
      Decl.Class(n, bs, ops.map((o, t) => o -> under(t, sc)))
    case Decl.Instance(c, fs)               => Decl.Instance(under(c, Nil), fs.map(f =>
        InstanceField(f.name, f.params.map(_ => blank), under(f.value, f.params.reverse))))
    case Decl.Namespace(n, ds)              => Decl.Namespace(n, ds.map(decl))
    case Decl.Budgeted(h, x)                => Decl.Budgeted(h, decl(x))
    case other                              => other
