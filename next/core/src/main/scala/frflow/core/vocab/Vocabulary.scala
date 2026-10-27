package frflow.core.vocab

import frflow.core.expr.Exprs
import frflow.core.name.{BoundaryName, DefName, ModelName, SymbolName, TypeName}
import frflow.core.ty.DataType

/** The signature a FrModel is written over: its domain types (opaque and declared), its symbols, its
  * defines, its boundaries and their models. Each name is declared once (`analysis.Validate` checks it).
  */
final case class Vocabulary(sorts: List[Sort], types: List[DataType], symbols: List[Symbol], defines: List[Define],
    boundaries: List[BoundarySig], models: List[StateModel]):
  def symbol(n: SymbolName): Option[Symbol] = symbols.find(_.name == n)
  def define(n: DefName): Option[Define] = defines.find(_.name == n)
  def dataType(n: TypeName): Option[DataType] = types.find(_.typeName == n)
  def boundary(n: BoundaryName): Option[BoundarySig] = boundaries.find(_.name == n)
  def model(n: ModelName): Option[StateModel] = models.find(_.name == n)

  /** `ds` and every define they call, each once, callers first. */
  def closure(ds: List[DefName]): List[Define] =
    def go(todo: List[DefName], seen: Set[DefName]): List[Define] = todo match
      case Nil                     => Nil
      case d :: rest if seen(d)    => go(rest, seen)
      case d :: rest               =>
        val called = define(d).toList.flatMap(x => Exprs.mentions(x.lambda.body).defines)
        define(d).toList ++ go(called ++ rest, seen + d)
    go(ds, Set.empty)
