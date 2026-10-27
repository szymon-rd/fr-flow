package frflow.core

import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.{Constructor, Selector}
import frflow.core.ty.{DataType, Field, Ty}

/** The tests' record type: a room booked from a start to an end, as Scala holds it. */
final case class Booking(room: String, start: BigInt, end: BigInt)

object Booking:
  val name: TypeName = TypeName("Booking")
  val ty: Ty = Ty.Data(name)
  val data: DataType = DataType.Product(name, "Booking", List(Field("room", Ty.Str), Field("start", Lang.big),
    Field("end", Lang.big)))
  val make: Constructor[String => BigInt => BigInt => Booking] =
    Constructor(name, CtorName("mk"), room => start => end => Booking(room, start, end))
  val start: Selector[Booking, BigInt] = Selector("start", 1, name, Lang.big, _.start, (b, v) => b.copy(start = v))
  val end: Selector[Booking, BigInt] = Selector("end", 2, name, Lang.big, _.end, (b, v) => b.copy(end = v))
