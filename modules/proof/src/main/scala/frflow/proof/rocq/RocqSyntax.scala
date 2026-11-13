package frflow.proof.rocq

import frflow.proof.prover.ast.{Binding, LOp, LPrefix, ProverName, Syntax}
import frflow.proof.rocq.RocqNames.Scope

/** A term as Rocq reads it: its text in a scope (the names bound around it), and what of its form the forms around
  * it read: a pattern's variables, a proof by a tactic, an input given by name.
  */
private[rocq] final case class RocqTerm(text: Scope => String, form: RocqTerm.Form = RocqTerm.Form.Other)

private[rocq] object RocqTerm:
  enum Form:
    case Other
    case Name(text: String)
    case Applied(head: RocqTerm, args: List[RocqTerm])
    case Parens(inner: RocqTerm)
    case Tupled(elems: List[RocqTerm])
    case Tactic(text: String)
    case Given(fn: RocqTerm, value: RocqTerm)

/** Rocq as an interpreter of the generated syntax. The lowering places the parentheses; what Rocq writes otherwise
  * than the notation is written here: a field read by its reader (`decisions_of limits`), a record with a field
  * replaced (`with_decisions limits ds`), an `if` on a proposition (`ite`), a pair's parts (`fst`, `snd`), a
  * quantifier over a list's members (`forall d, In d ds -> …`), a tuple and a product nested to the right.
  */
private[rocq] final class RocqSyntax(names: RocqNames) extends Syntax[RocqTerm]:
  import RocqTerm.Form
  private def of(text: Scope => String): RocqTerm = RocqTerm(text)

  def name(n: ProverName): RocqTerm = RocqTerm(s => names.name(n.text)(using s), Form.Name(n.text))
  def const(path: List[ProverName]): RocqTerm = of(s => names.constant(path.map(_.text))(using s))
  def ctor(data: ProverName, ctor: ProverName): RocqTerm = of(_ => RocqNames.constructor(data.text, ctor.text))
  def num(n: BigInt): RocqTerm = of(_ => if n < 0 then s"($n)" else n.toString)
  def str(s: String): RocqTerm = of(_ => "\"" + s.replace("\"", "\"\"") + "\"%string")
  def app(fn: RocqTerm, args: List[RocqTerm]): RocqTerm =
    RocqTerm(s => (fn :: args).map(_.text(s)).mkString(" "), Form.Applied(fn, args))
  def infix(op: LOp, a: RocqTerm, b: RocqTerm): RocqTerm = of(s => op match
    case LOp.Mem   => s"In (${a.text(s)}) (${b.text(s)})"
    case LOp.Times => s"(${a.text(s)} * (${b.text(s)}))%type"
    case other     => s"${a.text(s)} ${RocqSyntax.operators(other)} ${b.text(s)}")
  def prefix(op: LPrefix, a: RocqTerm): RocqTerm =
    of(s => (if op == LPrefix.Neg then "-" else "~ ") + s"(${a.text(s)})")
  def paren(inner: RocqTerm): RocqTerm = RocqTerm(s => s"(${inner.text(s)})", Form.Parens(inner))
  def dot(on: RocqTerm, field: String): RocqTerm = of(s => s"(${part(s"(${on.text(s)})", field)})")
  def tuple(elems: List[RocqTerm]): RocqTerm =
    RocqTerm(s => elems.map(_.text(s)).reduceRight((a, rest) => s"($a, $rest)"), Form.Tupled(elems))
  def listLit(elems: List[RocqTerm]): RocqTerm = of(s => elems.map(_.text(s)).mkString("[", "; ", "]"))
  def update(record: RocqTerm, fields: List[(ProverName, RocqTerm)]): RocqTerm = of(s =>
    fields.foldLeft(record.text(s))((got, f) => s"(${RocqNames.replacing(f._1.text)} $got (${f._2.text(s)}))"))
  def fun(params: List[Binding[RocqTerm]], body: RocqTerm): RocqTerm =
    of(s => s"fun ${params.map(binder(_)(s)).mkString(" ")} => ${body.text(over(params, s))}")
  def forall(params: List[Binding[RocqTerm]], body: RocqTerm): RocqTerm =
    of(quantified(params, body, ("forall", "->")))
  def exists(params: List[Binding[RocqTerm]], body: RocqTerm): RocqTerm =
    of(quantified(params, body, ("exists", "/\\")))
  def cond(c: RocqTerm, a: RocqTerm, b: RocqTerm): RocqTerm =
    of(s => s"(ite (${c.text(s)}) (${a.text(s)}) (${b.text(s)}))")
  def matching(on: RocqTerm, arms: List[(RocqTerm, RocqTerm)]): RocqTerm =
    of(s => s"match ${on.text(s)} with ${arms.map(arm(_, s)).mkString(" ")} end")
  def let(name: ProverName, ty: RocqTerm, value: RocqTerm, body: RocqTerm): RocqTerm = of { s =>
    val x = RocqNames.variable(name.text)
    s"let $x : ${ty.text(s)} := ${value.text(s)} in ${body.text(s.binding(List(name.text)))}"
  }
  def typed(e: RocqTerm, ty: RocqTerm): RocqTerm = of(s => s"(${e.text(s)} : ${ty.text(s)})")
  /** What an `exists` or a conjunction is given, one part after another; the last may be a tactic, given a
    * witness's time (one that does not go through must not run on).
    */
  def anonymous(elems: List[RocqTerm]): RocqTerm = of { s =>
    val parts = elems.map(e => e.form match
      case Form.Tactic(t) => s"timeout ${RocqDecl.witnessed} ($t)"
      case _              => s"frflow_give (${e.text(s)})")
    s"ltac:(${parts.mkString("; ")})"
  }
  def by(tactic: ProverName): RocqTerm = RocqTerm(_ => s"ltac:(${tactic.text})", Form.Tactic(tactic.text))
  def named(fn: RocqTerm, name: ProverName, value: RocqTerm): RocqTerm =
    RocqTerm(given_(fn, List(value)), Form.Given(fn, value))

  /** `e.f`: a pair's part, a list's length, else a record's field. */
  private def part(on: String, f: String): String = f match
    case "1"      => s"fst $on"
    case "2"      => s"snd $on"
    case "length" => s"Z.of_nat (List.length $on)"
    case field    => s"${RocqNames.field(field)} $on"

  def binder(b: Binding[RocqTerm])(s: Scope): String = b match
    case Binding.Explicit(n, t) => s"(${RocqNames.variable(n.text)} : ${t.text(s)})"
    case Binding.Several(ns, t) => s"(${ns.map(n => RocqNames.variable(n.text)).mkString(" ")} : ${t.text(s)})"
    case Binding.Implicit(n, t) => s"{${RocqNames.variable(n.text)} : ${t.text(s)}}"
    case Binding.Bare(n)        => RocqNames.variable(n.text)
    case Binding.Of(n, t)       => s"(${RocqNames.variable(n.text)} : ${t.text(s)})"
    case Binding.Member(n, _)   => RocqNames.variable(n.text)
    case Binding.Instance(c)    => s"`{${c.text(s)}}"

  private def over(ps: List[Binding[RocqTerm]], s: Scope): Scope = s.binding(ps.flatMap(_.bound.map(_.text)))

  /** A quantifier, one binder after another: a member of a list is a variable with what says it is one. `as` is
    * the quantifier's word, and what joins a member's being one to the body.
    */
  private def quantified(ps: List[Binding[RocqTerm]], body: RocqTerm, as: (String, String))(s: Scope): String =
    val (word, joins) = as
    ps match
      case Nil                               => body.text(s)
      case (m @ Binding.Member(_, in)) :: more =>
        s"$word ${binder(m)(s)}, In ${binder(m)(s)} (${in.text(s)}) $joins (${
          quantified(more, body, as)(over(List(m), s))})"
      case p :: more                         =>
        s"$word ${binder(p)(s)}, ${quantified(more, body, as)(over(List(p), s))}"

  /** A match's arm: its pattern's head a constructor, what it is applied to the variables it binds. */
  private def arm(a: (RocqTerm, RocqTerm), s: Scope): String =
    def named(ts: List[RocqTerm]): List[String] = ts.map(_.form).collect { case Form.Name(n) => n }
    val vars = a._1.form match
      case Form.Applied(_, args)                                => named(args)
      case Form.Parens(RocqTerm(_, Form.Applied(_, args)))      => named(args)
      case Form.Tupled(es)                                      => named(es)
      case _                                                    => Nil
    val inner = s.binding(vars)
    val pattern = a._1.form match
      case Form.Applied(head, args) => (head.text(s) :: args.map(_.text(inner))).mkString(" ")
      case _                        => a._1.text(inner)
    s"| $pattern => ${a._2.text(inner)}"

  /** `f (x := v) (h := p)`: a theorem with what it is given by name. Rocq gives no explicit input by name. The
    * lowering names every input, in the statement's order, so the theorem is applied to them in that order;
    * failing that, it is applied to what is to be proven, which fixes the inputs the statement names, and each
    * hypothesis left is one of the values given.
    */
  private def given_(fn: RocqTerm, values: List[RocqTerm])(s: Scope): String = fn.form match
    case Form.Given(f, v) => given_(f, v :: values)(s)
    case _                =>
      val vs = values.map(v => s"(${v.text(s)})")
      s"ltac:(first [exact (${fn.text(s)} ${vs.mkString(" ")}) | eapply (${fn.text(s)}); first [${
        vs.map(v => s"exact $v").mkString(" | ")}]])"

private[rocq] object RocqSyntax:
  val operators: Map[LOp, String] = Map(LOp.And -> "/\\", LOp.Or -> "\\/", LOp.Arrow -> "->", LOp.Iff -> "<->",
    LOp.Eq -> "=", LOp.Ne -> "<>", LOp.Add -> "+", LOp.Sub -> "-", LOp.Mul -> "*", LOp.Lt -> "<", LOp.Le -> "<=",
    LOp.Gt -> ">", LOp.Ge -> ">=", LOp.Append -> "++", LOp.Cons -> "::")
