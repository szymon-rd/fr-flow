package frflow.render

import frflow.ir.*
import frflow.ir.Expr.*

/** Prints IR as Lean source.
  *
  * Semantics of the translation (the trusted part of FrFlow, together with the
  * kernel prelude `FrFlow.Scala`):
  *   - `Boolean` is `Prop`; `&&`, `||`, `!`, `==` are `∧`, `∨`, `¬`, `=`.
  *   - `Int`, `Long` and `BigInt` are `Int` (no overflow; see the README).
  *   - `Map[K, V]` is `K → Option V` and `Set[A]` is `A → Prop`: both are compared
  *     extensionally, like Scala's immutable collections.
  *   - case classes are structures, enums are inductive types.
  * Non-atomic subterms are parenthesized, so precedence never matters.
  */
object LeanPrinter:

  // ---------------------------------------------------------------------------
  // Identifiers and literals
  // ---------------------------------------------------------------------------

  private val Keywords: Set[String] = Set(
    "abbrev", "at", "attribute", "axiom", "by", "calc", "catch", "class", "def", "deriving", "do", "else", "end",
    "example", "exists", "export", "extends", "finally", "for", "forall", "from", "fun", "have", "if", "import",
    "in", "inductive", "infix", "infixl", "infixr", "instance", "let", "local", "macro", "match", "mut", "mutual",
    "namespace", "noncomputable", "notation", "open", "opaque", "partial", "postfix", "prefix", "private",
    "protected", "return", "scoped", "section", "set_option", "show", "sorry", "structure", "syntax", "then",
    "theorem", "try", "unless", "universe", "unsafe", "variable", "where", "with", "admit", "break", "continue",
    "Type", "Prop", "Sort", "omit", "include", "termination_by", "decreasing_by", "using", "rec", "this"
  )

  private val Plain = """[A-Za-z_][A-Za-z0-9_']*""".r

  def isKeyword(s: String): Boolean = Keywords(s)

  def segment(s: String): String =
    if Keywords(s) || !Plain.matches(s) then s"«$s»" else s

  def ident(n: String): String = n.split('.').map(segment).mkString(".")

  def string(s: String): String =
    val sb = new StringBuilder("\"")
    s.foreach {
      case '"'          => sb ++= "\\\""
      case '\\'         => sb ++= "\\\\"
      case '\n'         => sb ++= "\\n"
      case '\t'         => sb ++= "\\t"
      case c if c < ' ' => sb ++= f"\\x${c.toInt}%02x"
      case c            => sb += c
    }
    sb += '"'
    sb.result()

  // ---------------------------------------------------------------------------
  // Types
  // ---------------------------------------------------------------------------

  def tpe(t: Type): String = t match
    case Type.Bool        => "Prop"
    case Type.Int         => "Int"
    case Type.Str         => "String"
    case Type.Unit        => "Unit"
    case Type.Named(n)    => ident(n)
    case Type.ListOf(e)   => s"List ${tpeArg(e)}"
    case Type.SetOf(e)    => s"Scala.Set ${tpeArg(e)}"
    case Type.MapOf(k, v) => s"Scala.Map ${tpeArg(k)} ${tpeArg(v)}"
    case Type.OptionOf(e) => s"Option ${tpeArg(e)}"
    case Type.TupleOf(es) => es.map(tpeArg).mkString(" × ")
    case Type.Fun(Nil, r) => s"Unit → ${tpe(r)}"
    case Type.Fun(ps, r)  => (ps.map(p => if p.isInstanceOf[Type.Fun] then s"(${tpe(p)})" else tpeArg(p)) :+ tpe(r)).mkString(" → ")

  private def tpeArg(t: Type): String = t match
    case Type.Bool | Type.Int | Type.Str | Type.Unit | Type.Named(_) => tpe(t)
    case _                                                         => s"(${tpe(t)})"

  def binder(p: Param): String = s"(${ident(p.name)} : ${tpe(p.tpe)})"
  def binders(ps: List[Param]): String = ps.map(binder).mkString(" ")

  // ---------------------------------------------------------------------------
  // Expressions
  // ---------------------------------------------------------------------------

  def atomic(e: Expr): Boolean = e match
    case Var(_) | BoolLit(_) | StrLit(_) | UnitLit | Ref(_) | Field(_, _) | With(_, _) => true
    case IntLit(v)                                                              => v >= 0
    case Construct(_, Nil)                                                      => true
    case Call(_, Nil, _)                                                        => true
    case PrimOp(Prim.ListNil | Prim.OptNone | Prim.SetEmpty | Prim.MapEmpty | Prim.TupleOf | Prim.ListOf |
          Prim.Fst | Prim.Snd, _, _) => true
    case _ => false

  def arg(e: Expr): String = if atomic(e) then expr(e) else s"(${expr(e)})"

  private def caseBody(e: Expr): String = e match
    case _: Match | _: Let => s"(${expr(e)})"
    case _                 => expr(e)

  def expr(e: Expr): String = e match
    case Var(n)             => ident(n)
    case BoolLit(b)         => if b then "True" else "False"
    case IntLit(v)          => v.toString
    case StrLit(s)          => string(s)
    case UnitLit            => "()"
    case Field(t, f)        => s"${arg(t)}.${segment(f)}"
    case Construct(c, Nil)  => ident(c)
    case Construct(c, as)   => (ident(c) :: as.map(arg)).mkString(" ")
    case With(t, us)        => s"{ ${arg(t)} with ${us.map((f, x) => s"${segment(f)} := ${expr(x)}").mkString(", ")} }"
    case Call(f, Nil, _)    => ident(f)
    case Call(f, as, _)     => (ident(f) :: as.map(arg)).mkString(" ")
    case Ref(n)             => ident(n)
    case PrimOp(op, as, t)  => prim(op, as, t)
    case Lam(Nil, b)        => s"fun (_ : Unit) => ${expr(b)}"
    case Lam(ps, b)         => s"fun ${binders(ps)} => ${expr(b)}"
    case App(f, Nil)        => s"${arg(f)} ()"
    case App(f, as)         => (arg(f) :: as.map(arg)).mkString(" ")
    case If(c, a, b)        => s"if ${expr(c)} then ${expr(a)} else ${expr(b)}"
    case Match(s, cs)       => s"match ${expr(s)} with ${cs.map(c => s"| ${pattern(c.pat)} => ${caseBody(c.body)}").mkString(" ")}"
    case Let(n, t, v, b)    => s"let ${ident(n)} : ${tpe(t)} := ${expr(v)}; ${expr(b)}"
    case Quant(q, ps, b) =>
      val sym = if q == Quantifier.All then "∀" else "∃"
      s"$sym ${binders(ps)}, ${expr(b)}"

  def pattern(p: Pattern): String = p match
    case Pattern.Wild                       => "_"
    case Pattern.Bind(n, Pattern.Wild)      => ident(n)
    case Pattern.Bind(n, q)                 => s"${ident(n)}@${patArg(q)}"
    case Pattern.Ctor("some", List(a))      => s"some ${patArg(a)}"
    case Pattern.Ctor("none", Nil)          => "none"
    case Pattern.Ctor("[]", Nil)            => "[]"
    case Pattern.Ctor("::", List(h, t))     => s"${patArg(h)} :: ${patArg(t)}"
    case Pattern.Ctor("tuple", as)          => as.map(pattern).mkString("(", ", ", ")")
    case Pattern.Ctor(c, Nil)               => ident(c)
    case Pattern.Ctor(c, as)                => (ident(c) :: as.map(patArg)).mkString(" ")
    case Pattern.Lit(e)                     => expr(e)

  private def patArg(p: Pattern): String = p match
    case Pattern.Wild | Pattern.Bind(_, Pattern.Wild) | Pattern.Ctor(_, Nil) | Pattern.Ctor("tuple", _) => pattern(p)
    case Pattern.Lit(IntLit(v)) if v >= 0                                                               => pattern(p)
    case Pattern.Lit(StrLit(_))                                                                         => pattern(p)
    case _                                                                                              => s"(${pattern(p)})"

  /** A one-parameter function as (binder, body): a lambda's own, or a fresh one. */
  private def unary(f: Expr): (Param, String) = f match
    case Lam(List(p), b) => (p, expr(b))
    case other =>
      val n = fresh("x", other.freeVars)
      (Param(n, Type.Unit), s"${arg(other)} ${ident(n)}")

  private def binderOf(p: Param): String = if p.tpe == Type.Unit then ident(p.name) else binder(p)

  private def fresh(base: String, avoid: Set[String]): String =
    (Iterator.single(base) ++ Iterator.from(1).map(i => s"$base$i")).find(n => !avoid(n)).get

  /** `fun x => decide (p x)`: a Prop-valued predicate as a Bool-valued one. */
  private def decideFn(f: Expr): String =
    val (p, body) = unary(f)
    s"(fun ${binderOf(p)} => decide ($body))"

  private def prim(op: Prim, as: List[Expr], t: Option[Type]): String =
    def a(i: Int): String = arg(as(i))
    def bin(sym: String): String = s"${a(0)} $sym ${a(1)}"
    def typed(text: String): String = t.fold(text)(ty => s"($text : ${tpe(ty)})")
    op match
      case Prim.And     => bin("∧")
      case Prim.Or      => bin("∨")
      case Prim.Not     => s"¬${a(0)}"
      case Prim.Implies => bin("→")
      case Prim.Eq      => bin("=")
      case Prim.Ne      => bin("≠")
      case Prim.Add     => bin("+")
      case Prim.Sub     => bin("-")
      case Prim.Mul     => bin("*")
      case Prim.Div     => s"Int.tdiv ${a(0)} ${a(1)}"
      case Prim.Mod     => s"Int.tmod ${a(0)} ${a(1)}"
      case Prim.Neg     => s"-${a(0)}"
      case Prim.Lt      => bin("<")
      case Prim.Le      => bin("≤")
      case Prim.Gt      => bin(">")
      case Prim.Ge      => bin("≥")
      case Prim.Max     => s"max ${a(0)} ${a(1)}"
      case Prim.Min     => s"min ${a(0)} ${a(1)}"
      case Prim.Concat  => bin("++")

      case Prim.ListNil        => typed("[]")
      case Prim.ListCons       => bin("::")
      case Prim.ListOf         => if as.isEmpty then typed("[]") else as.map(expr).mkString("[", ", ", "]")
      case Prim.ListAppend     => bin("++")
      case Prim.ListContains   => s"${a(1)} ∈ ${a(0)}"
      case Prim.ListForall =>
        val (p, body) = unary(as(1))
        s"∀ ${ident(p.name)} ∈ ${a(0)}, $body"
      case Prim.ListExists =>
        val (p, body) = unary(as(1))
        s"∃ ${ident(p.name)} ∈ ${a(0)}, $body"
      case Prim.ListMap        => s"List.map ${a(1)} ${a(0)}"
      case Prim.ListFilter     => s"List.filter ${decideFn(as(1))} ${a(0)}"
      case Prim.ListLength     => s"(List.length ${a(0)} : Int)"
      case Prim.ListIsEmpty    => s"${a(0)} = []"
      case Prim.ListNonEmpty   => s"${a(0)} ≠ []"
      case Prim.ListHeadOption => s"List.head? ${a(0)}"

      case Prim.OptSome      => s"some ${a(0)}"
      case Prim.OptNone      => typed("none")
      case Prim.OptGetOrElse => s"Option.getD ${a(0)} ${a(1)}"
      case Prim.OptIsDefined => s"${a(0)} ≠ none"
      case Prim.OptIsEmpty   => s"${a(0)} = none"
      case Prim.OptContains  => s"${a(0)} = some ${a(1)}"
      case Prim.OptExists =>
        val (p, body) = unary(as(1))
        s"∃ ${binderOf(p)}, ${a(0)} = some ${ident(p.name)} ∧ $body"
      case Prim.OptForall =>
        val (p, body) = unary(as(1))
        s"∀ ${binderOf(p)}, ${a(0)} = some ${ident(p.name)} → $body"
      case Prim.OptMap     => s"Option.map ${a(1)} ${a(0)}"
      case Prim.OptFlatMap => s"Option.bind ${a(0)} ${a(1)}"
      case Prim.OptOrElse  => s"Option.or ${a(0)} ${a(1)}"

      case Prim.SetEmpty     => typed("Scala.Set.empty")
      case Prim.SetOf        => typed(s"Scala.Set.ofList ${as.map(expr).mkString("[", ", ", "]")}")
      case Prim.SetContains  => s"${a(0)} ${a(1)}"
      case Prim.SetIncl      => s"Scala.Set.incl ${a(0)} ${a(1)}"
      case Prim.SetExcl      => s"Scala.Set.excl ${a(0)} ${a(1)}"
      case Prim.SetUnion     => s"Scala.Set.union ${a(0)} ${a(1)}"
      case Prim.SetIntersect => s"Scala.Set.inter ${a(0)} ${a(1)}"
      case Prim.SetDiff      => s"Scala.Set.diff ${a(0)} ${a(1)}"
      case Prim.SetForall =>
        val (p, body) = unary(as(1))
        s"∀ ${binderOf(p)}, ${a(0)} ${ident(p.name)} → $body"
      case Prim.SetExists =>
        val (p, body) = unary(as(1))
        s"∃ ${binderOf(p)}, ${a(0)} ${ident(p.name)} ∧ $body"
      case Prim.SetIsEmpty =>
        val x = fresh("x", as(0).freeVars)
        s"∀ ${ident(x)}, ¬${a(0)} ${ident(x)}"
      case Prim.SetSubsetOf =>
        val x = fresh("x", as(0).freeVars ++ as(1).freeVars)
        s"∀ ${ident(x)}, ${a(0)} ${ident(x)} → ${a(1)} ${ident(x)}"

      case Prim.MapEmpty     => typed("Scala.Map.empty")
      case Prim.MapGet       => s"${a(0)} ${a(1)}"
      case Prim.MapGetOrElse => s"Option.getD (${a(0)} ${a(1)}) ${a(2)}"
      case Prim.MapUpdated   => s"Scala.Map.updated ${a(0)} ${a(1)} ${a(2)}"
      case Prim.MapRemoved   => s"Scala.Map.removed ${a(0)} ${a(1)}"
      case Prim.MapContains  => s"${a(0)} ${a(1)} ≠ none"
      case Prim.MapIsEmpty =>
        val k = fresh("k", as(0).freeVars)
        s"∀ ${ident(k)}, ${a(0)} ${ident(k)} = none"
      case Prim.MapForall =>
        val (p, body) = unary(as(1))
        val x = ident(p.name)
        s"∀ ${binderOf(p)}, ${a(0)} $x.1 = some $x.2 → $body"
      case Prim.MapExists =>
        val (p, body) = unary(as(1))
        val x = ident(p.name)
        s"∃ ${binderOf(p)}, ${a(0)} $x.1 = some $x.2 ∧ $body"
      case Prim.MapKeySet => s"Scala.Map.keySet ${a(0)}"

      case Prim.TupleOf => as.map(expr).mkString("(", ", ", ")")
      case Prim.Fst     => s"${a(0)}.1"
      case Prim.Snd     => s"${a(0)}.2"
