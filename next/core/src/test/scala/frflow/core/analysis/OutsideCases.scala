package frflow.core.analysis

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.name.{NodeId, TypeName}
import frflow.core.term.Bound
import frflow.core.ty.{DataType, Field, Ty}
import frflow.core.analysis.outside.Premise

/** One theory per problem of the world outside, each the store's valid theory with one change. */
object OutsideCases:
  private def id(s: String) = NodeId(s)

  /** The claim about `book`'s runs no longer lists that runs on the store are atomic; the assumption saying it is
    * there.
    */
  val missing: ProblemCase = ProblemCase(Store.kb.unlinking(assumes("bookRuns", "oneAtATime")),
    List(Problem.PremiseMissing(id("bookRuns"), Premise.Atomic(Store.boundary), Some(id("oneAtATime")))))

  /** `always[Booking]`, and a record holding bookings by room in a map, where no guard reaches them yet. */
  private val byRoom = Ty.MapOf(Ty.Str, Booking.ty)
  private val unreached = Kb.of(claim("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always[Booking](Bound("b", Booking.ty))(b => l.s.eq(b, b)))))
    .declaring(_.copy(types = List(Booking.data, DataType.Product(TypeName("Shelf"), "Shelf",
      List(Field("byRoom", byRoom))))))

  val all: List[ProblemCase] = List(
    missing,
    ProblemCase(Store.kb.and(plain("unrelated")).linking(assumes("unrelated", "oneAtATime")),
      List(Problem.PremiseNotNeeded(id("unrelated"), id("oneAtATime")))),
    // The store with no model and nothing assumed of it: `book` calls it, and nothing says what it gives.
    ProblemCase(Store.kb.without("storeModel").without("oneAtATime").declaring(_.copy(models = Nil)),
      List(Problem.BoundaryUnchecked(Store.boundary))),
    ProblemCase(unreached, List(Problem.AlwaysNotReached(id("endsAfterStart"), byRoom,
      Problem.Place.Field("byRoom", "Shelf")))))
