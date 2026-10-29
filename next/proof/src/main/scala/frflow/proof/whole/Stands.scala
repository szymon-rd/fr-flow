package frflow.proof.whole

import frflow.core.analysis.{Callees, Resolved}
import frflow.core.code.Code
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.obligation.{Constant, Substitute}

/** What stands, in a statement of the theory as a whole, for each Definition among `symbols` that is not open: its
  * proven code (the define, or a program's run on the models) or its fixed value.
  */
object Stands:
  def of(r: Resolved, symbols: List[SymbolName]): Map[SymbolName, Substitute] =
    symbols.distinct.flatMap(s => r.theory.code.attached.get(s).map(_.code).collect {
      case Code.Valued(v)                       => s -> Substitute.Fixed(Constant(v, typeOf(r, s)))
      case Code.Proven(_) | Code.ProvenFlow(_) =>
        s -> Callees.ofDefinition(r.theory, s).flatMap(_.standsFor.get(s)).fold(Substitute.Nothing)(Substitute.Code(_))
    }).toMap

  private def typeOf(r: Resolved, s: SymbolName): Ty = r.theory.vocabulary.symbol(s).map(_.ty).collect {
    case SymbolType.Typed(t) => t
  }.getOrElse(Ty.Unit)
