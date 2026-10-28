package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.project.Projects
import frflow.project.pipeline.Contents
import frflow.proof.layout.NodeModules
import frflow.proof.lean.print.Print
import frflow.proof.obligation.Obligations
import frflow.proof.terms.TermTable

/** A log of the requests: a second store, its model, what it does and a rule about it, beside rooms. */
trait RequestLog[F[_], T[_]] derives BoundaryOps:
  def log(request: T[Booking]): F[Unit]

val requestLog = Boundary[RequestLog]("the log the requests are written to")

final class LoggedRequests[F[_]: Flow](state: Model[F, List[Booking]]) extends RequestLog[F, Term]:
  def log(request: Term[Booking]): F[Unit] = state.get.flatMap(logged => state.set(logged :+ request))

val loggedRequests = requestLog.model("every request logged, oldest first")(LoggedRequests(_))

/** A second program changing the table: the request added, granted or not. */
final class AddAnyway[F[_]](table: BookingTable[F, Term])(using f: Flow[F]):
  def run(request: Term[Booking]): F[Term[Unit]] = f.as(table.add(request), (): Term[Unit])

val addAnyway = Definition[Booking => Program[Unit]]("adding a request, granted or not")

/** One World, kept local (owner §19, §31): a statement takes only the rules of the stores it reads, so a store added
  * beside rooms brings back no statement that does not read it; and the programs changing a store are derived, so a
  * new one brings back the rules about the store, naming it.
  */
class StoresSuite extends munit.FunSuite:
  private val logMatchesModel = Node.assumption("The log adds each request at the end.")(
    requestLog.behavesAs(loggedRequests))
  private val logStartsEmpty = Node.assumption("The log starts empty.")(loggedRequests.initially(l => l === Nil))
  private val logOneAtATime = Node.assumption("Requests are logged one at a time.")(requestLog.atomic)
  private val loggedEndAfterStart = Node.claim("Every request logged ends after it starts.")(
    always(loggedRequests)(logged => logged.forall(b => b.start < b.end)))
    .assuming(logMatchesModel, logOneAtATime, logStartsEmpty)

  private def withNodes(extra: Node*): FrModel =
    FrModel("Rooms")((rooms.nodes ++ extra)*).copy(generators = rooms.generators)
      .implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))

  private val log = List(logMatchesModel, logOneAtATime, logStartsEmpty, loggedEndAfterStart)
  private val (was, now) = (Projects.bare(Projects.rooms), Projects.bare(Projects.elaborated(withNodes(log*))))
  // Its rule reaches every Booking, the log's too: it reads the log.
  private val reading = NodeId("bookingsEndAfterStart")
  private val ids = Projects.rooms.theory.nodes.map(_.node.id).filterNot(_ == reading)

  /** What Lean is given of a node: its modules, printed. */
  private def lean(a: frflow.project.pipeline.Analysis, id: NodeId): String =
    val r = a.canonical.resolved
    Obligations.of(r, TermTable.of(r), Set.empty).filter(_.node == id)
      .flatMap(NodeModules.of(r, TermTable.of(r), _)).map(Print.module).mkString("\n")

  test("a store added beside rooms, with a rule about it, changes no content of a statement not reading it") {
    assertEquals(whole.Theories.problems(withNodes(log*)), Nil)
    ids.foreach(id => assertEquals(Contents.of(now.canonical, id), Contents.of(was.canonical, id), id.value))
    assertNotEquals(Contents.of(now.canonical, reading), Contents.of(was.canonical, reading))
  }

  test("nor what Lean is asked of it: no obligation of a statement not reading the log takes the log's rule") {
    ids.foreach(id => assertNoDiff(lean(now, id), lean(was, id), id.value))
    assert(lean(now, NodeId("neverOverlap")).contains("cover_book") &&
      !lean(now, NodeId("neverOverlap")).contains("loggedRequests"))
    // What book keeps of every Booking is of the stores it reads: the log is its run's frame.
    assert(lean(now, reading).contains("cover_book") && !lean(now, reading).contains("loggedRequests"))
  }

  test("a second program changing the table: the rules reaching the table list it, derived, and only they") {
    def writers(m: FrModel) =
      val l = Projects.bare(Projects.elaborated(m)).canonical
      Projects.rooms.theory.nodes.map(_.node.id).map(id => id.value -> Contents.of(l, id).texts("writers"))
        .filter(_._2.nonEmpty)
    val addsIt = Node.claim("Adding a request stores it at the end.")(
      forall((request: Term[Booking], before: Term[World]) =>
        addAnyway(request).from(before) { (_, after) =>
          storedBookings.in(after) === storedBookings.in(before) :+ request }))
      .assuming(tableMatchesModel, oneAtATime, bookingsEndAfterStart)
    val adding = withNodes(addsIt).implementProven(addAnyway)(program { (request: Term[Booking]) =>
      AddAnyway(bookingTable.recording).run(request) })
    assertEquals(whole.Theories.problems(adding), Nil)
    assertEquals(writers(withNodes()), List("neverOverlap" -> List("book"), "bookingsEndAfterStart" -> List("book")))
    assertEquals(writers(adding), List("neverOverlap" -> List("book", "addAnyway"),
      "bookingsEndAfterStart" -> List("book", "addAnyway")))
  }
