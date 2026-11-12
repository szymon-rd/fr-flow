package frflow.core.analysis

import frflow.core.{Booking, Desk, Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.name.{NodeId, TypeName}
import frflow.core.term.Bound
import frflow.core.ty.{DataType, Field, Ty}
import frflow.core.analysis.outside.Premise

/** One theory per problem of the world outside, each the desk's valid theory with one change. */
object OutsideCases:
  private def id(s: String) = NodeId(s)

  /** A claim of `always[Booking]` where bookings come from outside (the desk is given them), no assumption saying
    * what those meet.
    */
  val missing: ProblemCase = ProblemCase(Desk.kb.and(always("endsAfterStart", claimed = true)),
    List(Problem.PremiseMissing(id("endsAfterStart"), Premise.FromOutside(Booking.ty), None)))

  /** `always[Booking]`, and a record holding bookings by room in a map, where no guard reaches them yet. */
  private val byRoom = Ty.MapOf(Ty.Str, Booking.ty)
  private val unreached = Kb.of(claim("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always[Booking](Bound("b", Booking.ty))(b => l.s.eq(b, b)))))
    .declaring(_.copy(types = List(Booking.data, DataType.Product(TypeName("Shelf"), "Shelf",
      List(Field("byRoom", byRoom))))))

  val all: List[ProblemCase] = List(
    missing,
    ProblemCase(Desk.kb.and(always("fromTheDesk", claimed = false), plain("unrelated"))
      .linking(assumes("unrelated", "fromTheDesk"), assumes("bookRuns", "fromTheDesk")),
      List(Problem.PremiseNotNeeded(id("unrelated"), id("fromTheDesk")))),
    ProblemCase(unreached, List(Problem.AlwaysNotReached(id("endsAfterStart"), byRoom,
      Problem.Place.Field("byRoom", "Shelf")))))
