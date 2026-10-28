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

/** A program reading the table and writing the log: the request's room read, the request logged. */
final class LogRequest[F[_]](table: BookingTable[F, Term], log: RequestLog[F, Term])(using f: Flow[F]):
  def run(request: Term[Booking]): F[Term[Unit]] =
    f.flatMap(table.inRoom(request.room))(_ => f.as(log.log(request), (): Term[Unit]))

val logRequest = Definition[Booking => Program[Unit]]("logging a request, once its room is read")

/** The log's nodes beside rooms: what the log does, its two facts, and a rule about it. */
object Logged:
  val logMatchesModel = Node.assumption("The log adds each request at the end.")(
    requestLog.behavesAs(loggedRequests))
  val logStartsEmpty = Node.assumption("The log starts empty.")(loggedRequests.initially(l => l === Nil))
  val logOneAtATime = Node.assumption("Requests are logged one at a time.")(requestLog.atomic)
  val loggedEndAfterStart = Node.claim("Every request logged ends after it starts.")(
    always(loggedRequests)(logged => logged.forall(b => b.start < b.end)))
    .assuming(logMatchesModel, logOneAtATime, logStartsEmpty)
  val log: List[Node] = List(logMatchesModel, logOneAtATime, logStartsEmpty, loggedEndAfterStart)

  /** Rooms with `extra` beside its nodes, its code attached as in `Knowledge.scala`. */
  def withNodes(extra: Node*): FrModel =
    FrModel("Rooms")((rooms.nodes ++ extra)*).copy(generators = rooms.generators)
      .implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))

/** One World, kept local (owner §19, §31): a statement takes only the rules of the stores it reads, so a store added
  * beside rooms brings back no statement that does not read it; and the programs changing a store are derived, so a
  * new one brings back the rules about the store, naming it.
  */
class StoresSuite extends munit.FunSuite:
  import Logged.*

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

  test("a program reading the table and writing the log keeps the log's rule, given both stores' rules") {
    val logsIt = Node.claim("Logging a request adds it to the log.")(
      forall((request: Term[Booking], before: Term[World]) =>
        logRequest(request).from(before) { (_, after) =>
          loggedRequests.in(after) === loggedRequests.in(before) :+ request }))
      .assuming(logMatchesModel, logOneAtATime, tableMatchesModel, oneAtATime, bookingsEndAfterStart)
    // Requests now reach the log from outside: the rule takes what the form sends.
    val loggedEndAfterStart = Node.claim("Every request logged ends after it starts.")(
      always(loggedRequests)(logged => logged.forall(b => b.start < b.end)))
      .assuming(logMatchesModel, logOneAtATime, logStartsEmpty, bookingsEndAfterStart)
    val nodes = List(logMatchesModel, logOneAtATime, logStartsEmpty, loggedEndAfterStart, logsIt)
    val m = withNodes(nodes*).implementProven(logRequest)(program { (request: Term[Booking]) =>
      LogRequest(bookingTable.recording, requestLog.recording).run(request) })
    assertEquals(whole.Theories.problems(m), Nil)
    val kept = lean(Projects.bare(Projects.elaborated(m)), NodeId("loggedEndAfterStart"))
    val keeps = kept.linesIterator.dropWhile(!_.contains("def keeps_logRequest")).take(2).mkString("\n")
    assert(kept.contains("cover_logRequest"), kept)
    // Its hypotheses: the table's rule and the log's, of the world before; its goal, the log's of the world after.
    assert(keeps.contains("(Rooms.neverOverlap before.bookingTable)"), keeps)
    assert(keeps.contains("(Rooms.loggedEndAfterStart before.requestLog)"), keeps)
    assert(keeps.contains("(Rooms.loggedEndAfterStart after.requestLog)"), keeps)
  }
