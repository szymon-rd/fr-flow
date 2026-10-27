package frflow.core.analysis

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.expr.OutsideFact
import frflow.core.name.{NodeId, TypeName}
import frflow.core.term.Bound
import frflow.core.ty.{DataType, Field, Ty}

/** One theory per problem of the world outside, each the store's valid theory with one change. */
object OutsideCases:
  private def id(s: String) = NodeId(s)

  /** The claim about `book`'s runs no longer lists that runs come one at a time; the assumption saying it is there. */
  val missing: ProblemCase = ProblemCase(Store.kb.unlinking(assumes("bookRuns", "oneAtATime")),
    List(Problem.PremiseMissing(id("bookRuns"), Premise.OneRunAtATime(Store.model), Some(id("oneAtATime")))))

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
    ProblemCase(Store.kb.and(outside("nobodyWrites")(OutsideFact.WrittenOnlyBy(Store.model, Nil))),
      List(Problem.WriterNotListed(Store.model, Store.book))),
    ProblemCase(unreached, List(Problem.AlwaysNotReached(id("endsAfterStart"), byRoom, "the field byRoom of Shelf"))))
