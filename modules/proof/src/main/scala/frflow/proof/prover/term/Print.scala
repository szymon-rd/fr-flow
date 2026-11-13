package frflow.proof.prover.term

import frflow.proof.prover.ast.*

/** Lean's text of the AST: a fold with no decision of its own (the lowering placed every parenthesis and line). */
object Print:
  def expr(e: LExpr): String = e match
    case LExpr.Name(n)            => n.text
    case LExpr.Const(path)        => path.map(_.text).mkString(".")
    case LExpr.Ctor(d, c)         => s"${d.text}.${c.text}"
    case LExpr.Num(n)             => n.toString
    case LExpr.Str(s)             => Names.string(s)
    case LExpr.App(f, as)         => (f :: as).map(expr).mkString(" ")
    case LExpr.Infix(op, a, b)    => s"${expr(a)} ${op.text} ${expr(b)}"
    case LExpr.Prefix(op, a)      => op.text + expr(a)
    case LExpr.Paren(i)           => s"(${expr(i)})"
    case LExpr.Dot(on, f)         => s"${expr(on)}.$f"
    case LExpr.Tuple(es)          => es.map(expr).mkString("(", ", ", ")")
    case LExpr.ListLit(es)        => es.map(expr).mkString("[", ", ", "]")
    case LExpr.Update(r, fs)      =>
      s"{ ${expr(r)} with ${fs.map((f, v) => s"${f.text} := ${expr(v)}").mkString(", ")} }"
    case LExpr.Fun(ps, b)         => s"fun ${binders(ps)} => ${expr(b)}"
    case LExpr.Forall(ps, b)      => s"∀ ${binders(ps)}, ${expr(b)}"
    case LExpr.Exists(ps, b)      => s"∃ ${binders(ps)}, ${expr(b)}"
    case LExpr.If(c, a, b)        => s"if ${expr(c)} then ${expr(a)} else ${expr(b)}"
    case LExpr.Match(on, arms)    =>
      s"match ${expr(on)} with ${arms.map((p, b) => s"| ${expr(p)} => ${expr(b)}").mkString(" ")}"
    case LExpr.Let(n, t, v, b)    => s"let ${n.text} : ${expr(t)} := ${expr(v)}; ${expr(b)}"
    case LExpr.Typed(x, t)        => s"(${expr(x)} : ${expr(t)})"
    case LExpr.Named(f, n, v)     => s"${expr(f)} (${n.text} := ${expr(v)})"
    case LExpr.Anonymous(es)      => es.map(expr).mkString("⟨", ", ", "⟩")
    case LExpr.By(t)              => s"by ${t.text}"

  def binder(b: LBinder): String = b match
    case LBinder.Explicit(n, t) => s"(${n.text} : ${expr(t)})"
    case LBinder.Several(ns, t) => s"(${ns.map(_.text).mkString(" ")} : ${expr(t)})"
    case LBinder.Implicit(n, t) => s"{${n.text} : ${expr(t)}}"
    case LBinder.Instance(c)    => s"[${expr(c)}]"
    case LBinder.Bare(n)        => n.text
    case LBinder.Of(n, _)       => n.text
    case LBinder.Member(n, in)  => s"${n.text} ∈ ${expr(in)}"

  def binders(bs: List[LBinder]): String = bs.map(binder).mkString(" ")
  private[prover] def params(bs: List[LBinder]): String = bs.map(" " + binder(_)).mkString

  private[prover] def dotted(ns: List[ProverName]): String = ns.map(_.text).mkString(".")
