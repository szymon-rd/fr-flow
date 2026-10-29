package frflow.core

import frflow.core.analysis.{Problem, Validate}
import frflow.core.code.{Attachment, Code, CodeTable}
import frflow.core.graph.Edge
import frflow.core.name.{KbName, NodeId, RelPath, Span, SymbolName}
import frflow.core.spec.Node
import frflow.core.ty.Ty
import frflow.core.vocab.{StateModel, Symbol, Vocabulary}

/** A theory written by hand, as elaboration gives it: its vocabulary, its nodes in order, its edges and its code. */
final case class Kb(vocabulary: Vocabulary, nodes: List[Node], edges: List[Edge], code: Map[SymbolName, Code]):
  def theory: Theory = Theory(KbName("Test"), vocabulary, nodes.zipWithIndex.map((n, i) => Sited(n, Span(Kb.file, i))),
    edges, CodeTable(code.map((s, c) => s -> Attachment(c, Kb.file)), Map.empty))
  def elaborated: Elaborated = Elaborated(theory, Map.empty, Nil)
  def problems: List[Problem] = Validate(elaborated).fold(_.toNonEmptyList.toList, _ => Nil)

  def and(more: Node*): Kb = copy(nodes = nodes ++ more)
  /** The theory without a node and the edges reaching it. */
  def without(id: String): Kb =
    copy(nodes = nodes.filterNot(_.id.value == id), edges = edges.filterNot(e => (e.from :: Kb.to(e) :: Nil)
      .exists(_.value == id)))
  def linking(more: Edge*): Kb = copy(edges = edges ++ more)
  def unlinking(e: Edge): Kb = copy(edges = edges.filterNot(_ == e))
  def coding(more: (SymbolName, Code)*): Kb = copy(code = code ++ more)
  def naming(more: Symbol*): Kb = copy(vocabulary = vocabulary.copy(symbols = vocabulary.symbols ++ more))
  def declaring(f: Vocabulary => Vocabulary): Kb = copy(vocabulary = f(vocabulary))
  /** Models declared, each operation a Definition its model gives the meaning (as elaboration gives them). */
  def modelling(ms: StateModel*): Kb = ms.foldLeft(this)((k, m) =>
    k.declaring(v => v.copy(models = v.models :+ m))
      .naming(m.ops.map(o => Nodes.definition(o.op.value, Kb.operation(o.params.map(_.ty), o.result)))*)
      .coding(m.ops.map(o => o.op -> Code.Modelled(m.name))*))

object Kb:
  val file: RelPath = RelPath.fromIdentifiers("src", "Model.scala")
  val empty: Kb = Kb(Vocabulary(Nil, Nil, Nil, Nil, Nil), Nil, Nil, Map.empty)
  def of(nodes: Node*): Kb = empty.and(nodes*)
  /** An operation's type: `A => Program[R]`, or `Program[R]` of none. */
  def operation(ins: List[Ty], result: Ty): Ty =
    if ins.isEmpty then Ty.FlowOf(result, None) else Ty.FnOf(ins, Ty.FlowOf(result, None))

  private def to(e: Edge): NodeId = e match
    case Edge.PartOf(_, w)   => w
    case Edge.Assumes(_, p)  => p
    case Edge.Replaces(_, o) => o
