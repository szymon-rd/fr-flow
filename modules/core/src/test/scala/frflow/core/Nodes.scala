package frflow.core

import cats.data.NonEmptyList
import frflow.core.graph.Edge
import frflow.core.name.{NodeId, RelPath, SourceText, SymbolName}
import frflow.core.spec.{Node, Reliance, Statement, Written}
import frflow.core.term.Bound
import frflow.core.term.language.Final
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType, ValueKind}

/** Nodes, edges and values as the DSL makes them, each named by its id. */
object Nodes:
  def claim(id: String)(f: Final[Boolean]): Node =
    Node(NodeId(id), s"$id holds.", Statement.Claim(Written.formula(f, SourceText(id)), Reliance.Relied))
  def assumption(id: String)(f: Final[Boolean]): Node =
    Node(NodeId(id), s"$id is assumed.", Statement.Assumption(Written.formula(f, SourceText(id))))
  /** `always[Booking]`: a rule of every booking, claimed or assumed. */
  def always(id: String, claimed: Boolean): Node =
    val f = Lang.formula([T[_]] => (l: Lang[T]) => l.s.always[Booking](Bound("b", Booking.ty))(_ => l.truth))
    if claimed then claim(id)(f) else assumption(id)(f)
  def design(id: String): Node =
    Node(NodeId(id), s"$id is decided.", Statement.Design(NonEmptyList.of(RelPath.fromIdentifiers("src", id))))
  /** A claim saying nothing about any value. */
  def plain(id: String): Node = claim(id)(Lang.truth)

  def partOf(part: String, whole: String): Edge = Edge.PartOf(NodeId(part), NodeId(whole))
  def assumes(node: String, premise: String): Edge = Edge.Assumes(NodeId(node), NodeId(premise))

  def definition(name: String, ty: Ty): Symbol =
    Symbol(SymbolName(name), s"what $name is", SymbolType.Typed(ty), ValueKind.Definition)
  def declaration(name: String, ty: Ty): Symbol =
    Symbol(SymbolName(name), s"what $name is", SymbolType.Typed(ty), ValueKind.Declaration)
  def codeOnly(name: String): Symbol =
    Symbol(SymbolName(name), s"what $name is", SymbolType.CodeOnly("Connection"), ValueKind.Definition)
