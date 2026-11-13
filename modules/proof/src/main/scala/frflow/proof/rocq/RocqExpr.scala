package frflow.proof.rocq

import frflow.proof.lean.ast.{LBinder, LExpr, LOp, LPrefix}
import frflow.proof.rocq.RocqNames.Scope

/** Rocq's text of a term of the generated AST. The lowering places the parentheses; what Rocq writes otherwise
  * than Lean is written here: a field read by its reader (`decisions_of limits`), a record with a field replaced
  * (`with_decisions limits ds`), an `if` on a proposition (`ite`), a pair's parts (`fst`, `snd`), a quantifier
  * over a list's members (`forall d, In d ds -> …`), a tuple and a product nested to the right, as Lean's are.
  */
private[rocq] final class RocqExpr(names: RocqNames):
  def apply(e: LExpr)(using Scope): String = e match
    case LExpr.Name(n)           => names.name(n.text)
    case LExpr.Const(path)       => names.constant(path.map(_.text))
    case LExpr.Ctor(d, c)        => RocqNames.constructor(d.text, c.text)
    case LExpr.Num(n)            => if n < 0 then s"($n)" else n.toString
    case LExpr.Str(s)            => "\"" + s.replace("\"", "\"\"") + "\"%string"
    case LExpr.Paren(i)          => s"(${apply(i)})"
    case LExpr.Typed(x, t)       => s"(${apply(x)} : ${apply(t)})"
    case LExpr.App(f, as)        => (f :: as).map(apply).mkString(" ")
    case LExpr.Tuple(es)         => es.map(apply).reduceRight((a, rest) => s"($a, $rest)")
    case LExpr.ListLit(es)       => es.map(apply).mkString("[", "; ", "]")
    case LExpr.By(t)             => s"ltac:(${t.text})"
    case other                   => shaped(other)

  private def shaped(e: LExpr)(using Scope): String = e match
    case LExpr.Infix(op, a, b)   => infix(op, a, b)
    case LExpr.Prefix(op, a)     => (if op == LPrefix.Neg then "-" else "~ ") + s"(${apply(a)})"
    case LExpr.Dot(on, f)        => s"(${part(s"(${apply(on)})", f)})"
    case LExpr.Update(r, fs)     =>
      fs.foldLeft(apply(r))((got, f) => s"(${RocqNames.replacing(f._1.text)} $got (${apply(f._2)}))")
    case LExpr.If(c, a, b)       => s"(ite (${apply(c)}) (${apply(a)}) (${apply(b)}))"
    case LExpr.Anonymous(es)     => given_(es)
    case n: LExpr.Named          => named(n, Nil)
    case other                   => binding(other)

  private def binding(e: LExpr)(using s: Scope): String = e match
    case LExpr.Fun(ps, b)        => s"fun ${ps.map(binder).mkString(" ")} => ${apply(b)(using over(ps))}"
    case LExpr.Forall(ps, b)     => quantified(ps, b)("forall", "->")
    case LExpr.Exists(ps, b)     => quantified(ps, b)("exists", "/\\")
    case LExpr.Let(n, t, v, b)   =>
      val x = RocqNames.variable(n.text)
      s"let $x : ${apply(t)} := ${apply(v)} in ${apply(b)(using s.binding(List(n.text)))}"
    case LExpr.Match(on, arms)   =>
      s"match ${apply(on)} with ${arms.map(arm).mkString(" ")} end"
    case other                   => throw RocqExpr.Unsupported(other.productPrefix)

  private def infix(op: LOp, a: LExpr, b: LExpr)(using Scope): String = op match
    case LOp.Mem   => s"In (${apply(a)}) (${apply(b)})"
    case LOp.Times => s"(${apply(a)} * (${apply(b)}))%type"
    case other     => s"${apply(a)} ${RocqExpr.operators(other)} ${apply(b)}"

  /** `e.f`: a pair's part, a list's length, else a record's field. */
  private def part(on: String, f: String): String = f match
    case "1"      => s"fst $on"
    case "2"      => s"snd $on"
    case "length" => s"Z.of_nat (List.length $on)"
    case field    => s"${RocqNames.field(field)} $on"

  def binder(b: LBinder)(using Scope): String = b match
    case LBinder.Explicit(n, t) => s"(${RocqNames.variable(n.text)} : ${apply(t)})"
    case LBinder.Several(ns, t) => s"(${ns.map(n => RocqNames.variable(n.text)).mkString(" ")} : ${apply(t)})"
    case LBinder.Implicit(n, t) => s"{${RocqNames.variable(n.text)} : ${apply(t)}}"
    case LBinder.Bare(n)        => RocqNames.variable(n.text)
    case LBinder.Of(n, t)       => s"(${RocqNames.variable(n.text)} : ${apply(t)})"
    case LBinder.Member(n, _)   => RocqNames.variable(n.text)
    case LBinder.Instance(c)    => s"`{${apply(c)}}"

  def over(ps: List[LBinder])(using s: Scope): Scope = s.binding(ps.flatMap(RocqExpr.bound))

  /** A quantifier, one binder after another: a member of a list is a variable with what says it is one. */
  private def quantified(ps: List[LBinder], body: LExpr)(word: String, joins: String)(using s: Scope): String =
    ps match
      case Nil                              => apply(body)
      case (m @ LBinder.Member(_, in)) :: more =>
        val inner = over(List(m))
        s"$word ${binder(m)}, In ${binder(m)} (${apply(in)}) $joins (${quantified(more, body)(word, joins)(using
          inner)})"
      case p :: more                        =>
        s"$word ${binder(p)}, ${quantified(more, body)(word, joins)(using over(List(p)))}"

  /** A match's arm: its pattern's head a constructor, what it is applied to the variables it binds. */
  private def arm(a: (LExpr, LExpr))(using s: Scope): String =
    val vars = a._1 match
      case LExpr.App(_, args)                   => args.collect { case LExpr.Name(n) => n.text }
      case LExpr.Paren(LExpr.App(_, args))      => args.collect { case LExpr.Name(n) => n.text }
      case LExpr.Tuple(es)                      => es.collect { case LExpr.Name(n) => n.text }
      case _                                    => Nil
    val pattern = a._1 match
      case LExpr.App(head, args) => (apply(head) :: args.map(apply(_)(using s.binding(vars)))).mkString(" ")
      case other                 => apply(other)(using s.binding(vars))
    s"| $pattern => ${apply(a._2)(using s.binding(vars))}"

  /** `⟨a, b, h⟩`: what an `exists` or a conjunction is given, one part after another; the last may be a tactic,
    * given a witness's time (one that does not go through must not run on).
    */
  private def given_(es: List[LExpr])(using Scope): String =
    val parts = es.map {
      case LExpr.By(t) => s"timeout ${RocqDecl.witnessed} (${t.text})"
      case part        => s"frflow_give (${apply(part)})"
    }
    s"ltac:(${parts.mkString("; ")})"

  /** `f (x := v) (h := p)`: a theorem with what it is given by name. Rocq gives no explicit input by name. The
    * lowering names every input, in the statement's order, so the theorem is applied to them in that order;
    * failing that, it is applied to what is to be proven, which fixes the inputs the statement names, and each
    * hypothesis left is one of the values given.
    */
  private def named(e: LExpr, values: List[LExpr])(using Scope): String = e match
    case LExpr.Named(f, _, v) => named(f, v :: values)
    case f                    =>
      val given_ = values.map(v => s"(${apply(v)})")
      s"ltac:(first [exact (${apply(f)} ${given_.mkString(" ")}) | eapply (${apply(f)}); first [${
        given_.map(v => s"exact $v").mkString(" | ")}]])"

private[rocq] object RocqExpr:
  /** A form of the generated AST Rocq is not printed from yet: a module that holds one is not printed. */
  final class Unsupported(val form: String) extends RuntimeException(s"FrFlow: no Rocq for $form yet")

  def bound(b: LBinder): List[String] = b match
    case LBinder.Explicit(n, _) => List(n.text)
    case LBinder.Several(ns, _) => ns.map(_.text)
    case LBinder.Implicit(n, _) => List(n.text)
    case LBinder.Bare(n)        => List(n.text)
    case LBinder.Of(n, _)       => List(n.text)
    case LBinder.Member(n, _)   => List(n.text)
    case LBinder.Instance(_)    => Nil

  val operators: Map[LOp, String] = Map(LOp.And -> "/\\", LOp.Or -> "\\/", LOp.Arrow -> "->", LOp.Iff -> "<->",
    LOp.Eq -> "=", LOp.Ne -> "<>", LOp.Add -> "+", LOp.Sub -> "-", LOp.Mul -> "*", LOp.Lt -> "<", LOp.Le -> "<=",
    LOp.Gt -> ">", LOp.Ge -> ">=", LOp.Append -> "++", LOp.Cons -> "::")
