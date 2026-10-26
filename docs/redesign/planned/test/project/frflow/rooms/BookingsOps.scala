package rooms

import cats.{Functor, Id}
import cats.syntax.all.*
import frflow.core.expr.Binder
import frflow.core.name.{BoundaryName, OpName, VarId}
import frflow.core.ty.Ty
import frflow.core.vocab.{ModelOp, OpSig}
import frflow.dsl.build.Declarations
import frflow.dsl.flow.{BoundaryOps, ReadRecording, Recorded, Terms}
import frflow.dsl.flow.Recording.given
import frflow.dsl.term.{LeanType, Term}

/** `Bookings`' operations as `BoundaryOps.derived` (a macro, `???` in the planned code) will make them, written by
  * hand as `RecordingSuite`'s `Store` is: the trait's signature, the recording instance a program needs, an adapter's
  * operation called by name (the model tests'), a model read from the developer's instance over its state, and the
  * adapter lifted as programs call it in production (each argument its term's value, each result its value's term).
  */
object BookingsOps extends BoundaryOps[Bookings]:
  private val booking = LeanType[Booking].ty
  def className: String = "Bookings"
  def ops: List[OpSig] = List(OpSig(OpName("inRoom"), List("room" -> Ty.Str), LeanType[RoomBookings].ty),
    OpSig(OpName("add"), List("booking" -> booking), Ty.Unit))
  def declares: Declarations = Declarations.none
  def recording(name: BoundaryName): Bookings[Recorded, Term] = new Bookings[Recorded, Term]:
    def inRoom(room: Term[String]): Recorded[Term[RoomBookings]] = recorded(name, "inRoom", room)
    def add(booking: Term[Booking]): Recorded[Unit] = recorded[Unit](name, "add", booking).void
  def call[F[_]: Functor](adapter: Bookings[F, Id], op: OpName, args: List[Any]): F[Any] = (op.value, args) match
    case ("inRoom", List(room: String))  => adapter.inRoom(room).widen
    case ("add", List(booking: Booking)) => adapter.add(booking).widen
    case _                               => throw IllegalArgumentException(s"no ${op.value} on Bookings")
  def lifted[F[_]: Functor](adapter: Bookings[F, Id], values: Terms): Bookings[F, Term] = new Bookings[F, Term]:
    def inRoom(room: Term[String]): F[Term[RoomBookings]] = adapter.inRoom(values.value(room)).map(values.term(_))
    def add(booking: Term[Booking]): F[Unit] = adapter.add(values.value(booking))
  def model(instance: Bookings[Recorded, Term]): List[ModelOp] =
    val (room, b) = (Binder(VarId.level(0), "room", Ty.Str), Binder(VarId.level(0), "booking", booking))
    List(ModelOp(OpName("inRoom"), List(room), ReadRecording.steps(instance.inRoom(Term.free(room)))._1),
      ModelOp(OpName("add"), List(b), ReadRecording.steps(instance.add(Term.free(b)))._1))

  private def recorded[R: LeanType](b: BoundaryName, op: String, args: Term[?]*): Recorded[Term[R]] =
    Recorded.Call(b, OpName(op), args.toList, LeanType[R])
