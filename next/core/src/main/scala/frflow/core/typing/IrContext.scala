package frflow.core.typing

import frflow.core.name.{DefName, ModelName, SymbolName, TypeName}
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.{OpSig, SymbolType, Vocabulary}

/** What the IR's checker reads its terms against: the domain's types, each define's type, whether a symbol is the
  * vocabulary's at a type, each operation's signature, each model's state.
  */
final case class IrContext(data: TypeName => Option[DataType], defines: DefName => Option[Ty],
    symbols: (SymbolName, Ty) => Boolean, operations: SymbolName => Option[OpSig], states: ModelName => Option[Ty])

object IrContext:
  /** A theory's vocabulary: every symbol at its type, every define and operation known. */
  def of(v: Vocabulary): IrContext = IrContext(v.dataType, d => v.define(d).map(defined =>
    defined.lambda.params match
      case Nil => defined.lambda.result
      case ps  => Ty.FnOf(ps.map(_.ty), defined.lambda.result)),
    (n, t) => v.symbol(n).exists(s => s.ty == SymbolType.Typed(t) || codeOnly(s.ty)),
    op => v.modelOf(op).flatMap(_.op(op)).map(_.sig), m => v.model(m).map(_.state))

  /** A value only plain code reads: no Lean type to check it at; a statement mentioning it is refused by `Validate`
    * (`CodeOnlyInStatement`), which runs after this check.
    */
  private def codeOnly(t: SymbolType): Boolean = t match
    case SymbolType.CodeOnly(_) => true
    case SymbolType.Typed(_)    => false

  /** Terms over no vocabulary (the laws'): a symbol at the type it is used at, no operations or models. */
  def open(data: TypeName => Option[DataType], defines: DefName => Option[Ty]): IrContext =
    IrContext(data, defines, (_, _) => true, _ => None, _ => None)
