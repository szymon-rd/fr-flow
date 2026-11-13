package frflow.proof.prover.term

import frflow.proof.prover.ast.*

/** The notation a node's content is signed in, as an interpreter of the syntax: a term is its text. It decides
  * nothing: the lowering placed every parenthesis.
  */
object Notation extends Syntax[String]:
  def name(n: ProverName): String = n.text
  def const(path: List[ProverName]): String = path.map(_.text).mkString(".")
  def ctor(data: ProverName, ctor: ProverName): String = s"${data.text}.${ctor.text}"
  def num(n: BigInt): String = n.toString
  def str(s: String): String = Names.string(s)
  def app(fn: String, args: List[String]): String = (fn :: args).mkString(" ")
  def infix(op: LOp, left: String, right: String): String = s"$left ${op.text} $right"
  def prefix(op: LPrefix, arg: String): String = op.text + arg
  def paren(inner: String): String = s"($inner)"
  def dot(on: String, field: String): String = s"$on.$field"
  def tuple(elems: List[String]): String = elems.mkString("(", ", ", ")")
  def listLit(elems: List[String]): String = elems.mkString("[", ", ", "]")
  def update(record: String, fields: List[(ProverName, String)]): String =
    s"{ $record with ${fields.map((f, v) => s"${f.text} := $v").mkString(", ")} }"
  def fun(params: List[Binding[String]], body: String): String = s"fun ${binders(params)} => $body"
  def forall(params: List[Binding[String]], body: String): String = s"∀ ${binders(params)}, $body"
  def exists(params: List[Binding[String]], body: String): String = s"∃ ${binders(params)}, $body"
  def cond(c: String, ifTrue: String, ifFalse: String): String = s"if $c then $ifTrue else $ifFalse"
  def matching(on: String, arms: List[(String, String)]): String =
    s"match $on with ${arms.map((p, b) => s"| $p => $b").mkString(" ")}"
  def let(name: ProverName, ty: String, value: String, body: String): String =
    s"let ${name.text} : $ty := $value; $body"
  def typed(e: String, ty: String): String = s"($e : $ty)"
  def anonymous(elems: List[String]): String = elems.mkString("⟨", ", ", "⟩")
  def by(tactic: ProverName): String = s"by ${tactic.text}"
  def named(fn: String, name: ProverName, value: String): String = s"$fn (${name.text} := $value)"

  def binder(b: Binding[String]): String = b match
    case Binding.Explicit(n, t) => s"(${n.text} : $t)"
    case Binding.Several(ns, t) => s"(${ns.map(_.text).mkString(" ")} : $t)"
    case Binding.Implicit(n, t) => s"{${n.text} : $t}"
    case Binding.Instance(c)    => s"[$c]"
    case Binding.Bare(n)        => n.text
    case Binding.Of(n, _)       => n.text
    case Binding.Member(n, in)  => s"${n.text} ∈ $in"

  def binders(bs: List[Binding[String]]): String = bs.map(binder).mkString(" ")
