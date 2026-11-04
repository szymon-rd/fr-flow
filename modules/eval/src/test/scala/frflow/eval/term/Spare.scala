package frflow.eval.term

import frflow.core.Lang
import frflow.core.name.TypeName
import frflow.core.term.Selector
import frflow.core.ty.{DataType, Field, Ty}

/** A record of the Lean law with an option field: a field read off a constant of it is typed (`LeanTerm.field`). */
final case class Spare(at: Option[BigInt])

object Spare:
  val name: TypeName = TypeName("Spare")
  val ty: Ty = Ty.Data(name)
  val data: DataType = DataType.Product(name, "Spare", List(Field("at", Ty.OptionOf(Lang.big))))
  val at: Selector[Spare, Option[BigInt]] =
    Selector("at", 0, name, Ty.OptionOf(Lang.big), _.at, (s, v) => s.copy(at = v))
