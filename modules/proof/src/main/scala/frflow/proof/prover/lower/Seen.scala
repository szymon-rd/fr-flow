package frflow.proof.prover.lower

import frflow.proof.prover.ast.*
import frflow.proof.prover.ast.Tree.into
import frflow.proof.prover.term.Gathered

/** What a term already written is, as far as the one writing around it asks: a list written out is grown in place,
  * a call takes one more input inside its parentheses, a field of a record made on the spot is the input it was
  * made of.
  */
enum Shape[+E]:
  /** A list written out, its elements. */
  case Listed(elems: List[E])
  /** `(e : T)`; `empty`, of the empty list. */
  case Typed(empty: Boolean)
  /** A constructor of a domain type, the type's name. */
  case Ctor(data: ProverName)
  /** `f a b`, and in its parentheses `(f a b)`, as every call is generated. */
  case Applied(fn: E, args: List[E])
  case Call(fn: E, args: List[E])
  case Other

/** What the one written into tells of a term written: `E` is any interpreter's, so nothing is read off a term but
  * what its interpreter says here. The lowering writes into a `Syntax[E]` and asks a `Seen[E]`, and so is one for
  * every `E`: the tree (`Seen.tree`), or a text with what it is beside it (`term.Shaped`).
  */
trait Seen[E]:
  def shape(e: E): Shape[E]
  /** The identifiers it names where one is received: those a helper or a membership binder must not take. */
  def names(e: E): Set[String]

object Seen:
  /** The tree's own: its top node, and its identifiers by the reading every interpreter has (`Identifiers`). */
  given tree: Seen[LExpr] with
    def shape(e: LExpr): Shape[LExpr] = e match
      case LExpr.ListLit(es)                  => Shape.Listed(es)
      case LExpr.Typed(LExpr.ListLit(Nil), _) => Shape.Typed(empty = true)
      case LExpr.Typed(_, _)                  => Shape.Typed(empty = false)
      case LExpr.Ctor(d, _)                   => Shape.Ctor(d)
      case LExpr.App(f, as)                   => Shape.Applied(f, as)
      case LExpr.Paren(LExpr.App(f, as))      => Shape.Call(f, as)
      case _                                  => Shape.Other
    def names(e: LExpr): Set[String] = e.into(Identifiers)

/** The identifiers a term names where one is received: binders and blocks are not receivers, and say none. */
object Identifiers extends Gathered[Set[String]]:
  override def name(n: ProverName): Set[String] = Set(n.text)
  override def const(path: List[ProverName]): Set[String] = path.headOption.map(_.text).toSet
  override def ctor(data: ProverName, ctor: ProverName): Set[String] = Set(data.text)
  override def update(record: Set[String], fields: List[(ProverName, Set[String])]): Set[String] = Set.empty
  override def fun(params: List[Binding[Set[String]]], body: Set[String]): Set[String] = Set.empty
  override def forall(params: List[Binding[Set[String]]], body: Set[String]): Set[String] = Set.empty
  override def exists(params: List[Binding[Set[String]]], body: Set[String]): Set[String] = Set.empty
  override def matching(on: Set[String], arms: List[(Set[String], Set[String])]): Set[String] = Set.empty
  override def let(name: ProverName, ty: Set[String], value: Set[String], body: Set[String]): Set[String] =
    Set.empty
  override def anonymous(elems: List[Set[String]]): Set[String] = Set.empty
  override def named(fn: Set[String], name: ProverName, value: Set[String]): Set[String] = Set.empty
