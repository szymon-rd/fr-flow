package frflow.proof.lean.laws

import frflow.proof.lean.ast.*

/** Lean read back (`LeanReader`) with every bound variable replaced by its de Bruijn index (`#0` the innermost) and
  * every binder's name by `_`: two terms that differ only in how their variables are named read the same, and a
  * name a binder captures reads as an index where it should read as itself. Binders: `∀`, `∃`, `fun` (typed, bare
  * and membership binders), `let`, and a `match` arm's pattern variables (the arguments of its constructor, the
  * components of a pair; `_`).
  */
object DeBruijn:
  def apply(e: LExpr): LExpr = go(e, Nil)

  /** The names left free, in order met, each as often as it occurs. */
  def free(e: LExpr): List[String] = names(apply(e)).filterNot(_.startsWith("#"))

  private val blank = LeanName.unsafe("_")
  private def index(n: LeanName, scope: List[LeanName]): LExpr =
    val i = scope.indexOf(n)
    LExpr.Name(if i < 0 then n else LeanName.unsafe(s"#$i"))

  private def go(e: LExpr, scope: List[LeanName]): LExpr = e match
    case LExpr.Name(n)             => index(n, scope)
    case LExpr.App(f, as)          => LExpr.App(go(f, scope), as.map(go(_, scope)))
    case LExpr.Infix(op, a, b)     => LExpr.Infix(op, go(a, scope), go(b, scope))
    case LExpr.Prefix(op, a)       => LExpr.Prefix(op, go(a, scope))
    case LExpr.Paren(i)            => LExpr.Paren(go(i, scope))
    case LExpr.Dot(on, f)          => LExpr.Dot(go(on, scope), f)
    case LExpr.Tuple(es)           => LExpr.Tuple(es.map(go(_, scope)))
    case LExpr.ListLit(es)         => LExpr.ListLit(es.map(go(_, scope)))
    case LExpr.Update(r, fs)       => LExpr.Update(go(r, scope), fs.map((f, v) => f -> go(v, scope)))
    case LExpr.Typed(x, t)         => LExpr.Typed(go(x, scope), go(t, scope))
    case LExpr.If(c, a, b)         => LExpr.If(go(c, scope), go(a, scope), go(b, scope))
    case LExpr.Fun(ps, b)          => bind(ps, b, scope)(LExpr.Fun(_, _))
    case LExpr.Forall(ps, b)       => bind(ps, b, scope)(LExpr.Forall(_, _))
    case LExpr.Exists(ps, b)       => bind(ps, b, scope)(LExpr.Exists(_, _))
    case LExpr.Let(n, t, v, b)     => LExpr.Let(blank, go(t, scope), go(v, scope), go(b, n :: scope))
    case LExpr.Match(on, arms)     => LExpr.Match(go(on, scope), arms.map((p, b) =>
        val bound = patternVariables(p)
        (blanked(p, bound.toSet), go(b, bound.reverse ++ scope))))
    case other                     => other

  /** The binders in turn, each type (and a membership binder's list) read where the binder stands. */
  private def bind(ps: List[LBinder], body: LExpr, scope: List[LeanName])(make: (List[LBinder], LExpr) => LExpr)
      : LExpr =
    val (out, inner) = ps.foldLeft((List.empty[LBinder], scope)) { case ((done, sc), p) => p match
      case LBinder.Explicit(n, t) => (done :+ LBinder.Explicit(blank, go(t, sc)), n :: sc)
      case LBinder.Bare(n)        => (done :+ LBinder.Bare(blank), n :: sc)
      case LBinder.Member(n, in)  => (done :+ LBinder.Member(blank, go(in, sc)), n :: sc)
      case LBinder.Several(ns, t) => (done :+ LBinder.Several(ns.map(_ => blank), go(t, sc)), ns.reverse ++ sc)
      case other                  => (done :+ other, sc)
    }
    make(out, go(body, inner))

  /** A pattern's variables, in order: a constructor's arguments, a pair's components, `_`. */
  private def patternVariables(p: LExpr): List[LeanName] = p match
    case LExpr.Paren(i)                 => patternVariables(i)
    case LExpr.App(_, as)               => as.flatMap(variable)
    case LExpr.Tuple(es)                => es.flatMap(e => variable(e).toList ++ patternVariables(e))
    case LExpr.Name(n) if n.text == "_" => List(n)
    case _                              => Nil

  private def variable(e: LExpr): Option[LeanName] = e match
    case LExpr.Name(n) => Some(n)
    case _             => None

  private def blanked(p: LExpr, bound: Set[LeanName]): LExpr = p match
    case LExpr.Name(n) if bound(n) => LExpr.Name(blank)
    case LExpr.Paren(i)            => LExpr.Paren(blanked(i, bound))
    case LExpr.App(f, as)          => LExpr.App(f, as.map(blanked(_, bound)))
    case LExpr.Tuple(es)           => LExpr.Tuple(es.map(blanked(_, bound)))
    case other                     => other

  private def names(e: LExpr): List[String] = e match
    case LExpr.Name(n)          => List(n.text)
    case LExpr.App(f, as)       => (f :: as).flatMap(names)
    case LExpr.Infix(_, a, b)   => names(a) ++ names(b)
    case LExpr.Prefix(_, a)     => names(a)
    case LExpr.Paren(i)         => names(i)
    case LExpr.Dot(on, _)       => names(on)
    case LExpr.Tuple(es)        => es.flatMap(names)
    case LExpr.ListLit(es)      => es.flatMap(names)
    case LExpr.Update(r, fs)    => names(r) ++ fs.flatMap(f => names(f._2))
    case LExpr.Typed(x, t)      => names(x) ++ names(t)
    case LExpr.If(c, a, b)      => List(c, a, b).flatMap(names)
    case LExpr.Fun(ps, b)       => ps.flatMap(binderNames) ++ names(b)
    case LExpr.Forall(ps, b)    => ps.flatMap(binderNames) ++ names(b)
    case LExpr.Exists(ps, b)    => ps.flatMap(binderNames) ++ names(b)
    case LExpr.Let(_, t, v, b)  => List(t, v, b).flatMap(names)
    case LExpr.Match(on, arms)  => names(on) ++ arms.flatMap((_, b) => names(b))
    case _                      => Nil

  private def binderNames(b: LBinder): List[String] = b match
    case LBinder.Explicit(_, t) => names(t)
    case LBinder.Member(_, in)  => names(in)
    case LBinder.Several(_, t)  => names(t)
    case _                      => Nil
