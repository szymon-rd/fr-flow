package frflow.core.analysis

import frflow.core.name.{NodeId, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.{SymbolType, ValueKind}
import frflow.core.Theory

/** What a statement constrains (owner §15): every Declaration and Definition it mentions, through the defines it
  * calls. The code defining a Definition is checked against it; the code calling one assumes it.
  */
object Constrained:
  def of(t: Theory, id: NodeId): List[SymbolName] =
    Resolve.mentions(t, id).symbols.filter(t.vocabulary.symbol(_).nonEmpty)

  /** A function's or a program's: what code calls. */
  def isFunction(t: Theory, s: SymbolName): Boolean = t.vocabulary.symbol(s).map(_.ty).exists {
    case SymbolType.Typed(Ty.FnOf(_, _) | Ty.FlowOf(_, _)) => true
    case _                                                 => false
  }

  /** A value only plain code reads (a connection): it has no Lean type, so no statement can mention it. */
  def isCodeOnly(t: Theory, s: SymbolName): Boolean = codeOnlyType(t, s).nonEmpty

  /** The Scala type of a value only plain code reads, which has no Lean type. */
  def codeOnlyType(t: Theory, s: SymbolName): Option[String] = t.vocabulary.symbol(s).map(_.ty).collect {
    case SymbolType.CodeOnly(scala) => scala
  }

  def isDeclaration(t: Theory, s: SymbolName): Boolean =
    t.vocabulary.symbol(s).exists(_.kind == ValueKind.Declaration)

  /** The statements constraining `s`: its claims and assumptions. */
  def statements(t: Theory, s: SymbolName): List[NodeId] = t.nodes.map(_.node.id).filter(of(t, _).contains(s))
