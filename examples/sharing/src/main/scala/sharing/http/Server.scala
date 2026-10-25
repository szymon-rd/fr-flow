package sharing.http

import cats.effect.SyncIO
import com.sun.net.httpserver.{HttpExchange, HttpServer}
import frflow.{Clock, FakeClock, FaultPlan, FlowFailed, SystemClock}
import io.circe.Json
import java.net.{InetSocketAddress, URLDecoder}
import java.nio.charset.StandardCharsets.UTF_8
import java.util.concurrent.atomic.AtomicReference
import java.util.concurrent.{ExecutorService, Executors, TimeUnit, TimeoutException}
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.knowledge
import sharing.notifications.{Mailer, MemoryMailer, Notifications}
import sharing.store.{LibraryStore, MemoryLibraryStore, SqlLibraryStore}

/** The service on a store, a mail server and a clock: HandleContract's proven flow, HousekeepingJob's and DeliveryJob's,
  * run on them, one at a time (each reads the library the last one left). A flow that fails (the store or the mail
  * server down) changed nothing it was proven not to change; a request is then answered 503, a job's run is tried again
  * at its next tick. `faults`: failures to inject into the store's and the mail server's next calls (tests, and the
  * scripted session).
  */
final class StoreHttp(s: LibraryStore, val clock: Clock = SystemClock, val mailer: MemoryMailer = MemoryMailer()) extends SharingHttp:
  private val faults = AtomicReference(FaultPlan(Nil))
  /** The next calls of the store and the mail server fail as `fs` says, in order (`true`: that call fails). */
  def failNext(fs: List[Boolean]): Unit = faults.set(FaultPlan(fs))
  private val store: LibraryStore = new LibraryStore:
    def load = faults.get.apply(LibraryStore.store, s).load
    def save(l: frflow.Term[Library]) = faults.get.apply(LibraryStore.store, s).save(l)
  private val mail: Mailer = new Mailer:
    def send(n: frflow.Term[Notice]) = faults.get.apply(Notifications.mailer, mailer: Mailer).send(n)
  private val bound = Seq(LibraryStore.store.bind(store), Notifications.mailer.bind(mail), Clock.boundary.bind(clock))
  private val run = knowledge.run[SyncIO](SharingHttp.handleContract)(bound*)
  private val job = knowledge.run[SyncIO](Housekeeping.jobContract)(bound*)
  private val delivery = knowledge.run[SyncIO](Notifications.deliveryJob)(bound*)
  /** The answer, or why the flow failed. */
  def attempt(request: Request): Either[Failure, Answer] =
    synchronized(run(request).attempt.unsafeRunSync()).left.map { case FlowFailed(f: Failure) => f; case e => throw e }
  /** A failure is the server's 503: `Server.answer` turns it into one. */
  def handle(request: Request): Answer = attempt(request).fold(f => throw FlowFailed(f), identity)
  /** A run of housekeeping; false when it failed (it changed nothing). */
  def housekeep(): Boolean = synchronized(job().attempt.unsafeRunSync()).isRight
  /** A run of delivery; false when it failed (the notice stays in the outbox). */
  def deliver(): Boolean = synchronized(delivery().attempt.unsafeRunSync()).isRight
  /** What the store holds now (for the testing routes). */
  def held: Library = s match
    case m: MemoryLibraryStore => m.library
    case q: SqlLibraryStore    => q.library
    case _                     => throw IllegalStateException("a store the server cannot read back")

/** Housekeeping on the computer's clock: `Housekeeping.schedule` (every minute) on a thread of its own. Each run's start
  * is checked against HousekeepingOnTime, the deadlines' assumption: a gap longer than it is logged.
  */
object Scheduler:
  def start(service: StoreHttp): Thread =
    val within = BigInt(120) // HousekeepingPeriod: Run.housekeepingWithin
    var last = Option.empty[BigInt]
    def started(t: BigInt): Unit =
      last.filter(l => t - l > within).foreach(l => System.err.println(s"sharing: HousekeepingOnTime broken: ${t - l} s since the last run"))
      last = Some(t)
    val loop = Housekeeping.schedule.schedule[SyncIO](service.clock, None, started)(() => SyncIO {
      if !service.housekeep() then System.err.println("sharing: housekeeping failed; it is tried again at the next minute")
    })
    val deliveries = Notifications.schedule.schedule[SyncIO](service.clock, None)(() => SyncIO(service.deliver()).void)
    val thread = Thread(() => try loop.unsafeRunSync() catch case _: InterruptedException => ())
    thread.setDaemon(true)
    thread.setName("sharing-housekeeping")
    thread.start()
    val sender = Thread(() => try deliveries.unsafeRunSync() catch case _: InterruptedException => ())
    sender.setDaemon(true)
    sender.setName("sharing-delivery")
    sender.start()
    thread

/** The service over HTTP on localhost. Requests run on a pool of workers, each with a time limit (503 past it); an
  * internal error is answered 500 and logged with the request, never a dropped connection. ServerWiring governs it.
  */
object Server:
  // Answers go out as written: without it, a small answer waits on the client's delayed ACK (about 40 ms).
  System.setProperty("sun.net.httpserver.nodelay", "true")

  /** One request answered: what the server sends, and what the tests call without a socket. */
  def answer(service: SharingHttp, method: String, path: String, query: Map[String, String], body: String): (Int, String) =
    val (status, json) = HttpCodec.request(method, path, query, body).fold(HttpCodec.reply, r =>
      try HttpCodec.reply(service.handle(r)) catch case FlowFailed(f: Failure) => HttpCodec.reply(f))
    (status, json.noSpaces)

  /** With a fake clock, the routes a test drives time and failures with: `POST /clock {"advance":seconds}` moves it on
    * and answers the time; `POST /housekeep` and `POST /deliver` run housekeeping and delivery once, as the schedulers
    * would; `POST /faults {"fail":[false,true]}` makes the next calls of the store and the mail server fail as listed;
    * `GET /log`, `GET /outbox`, `GET /requests` and `GET /mailbox` show what the store and the mail server hold.
    */
  def testing(service: StoreHttp, clock: FakeClock, method: String, path: String, body: String): Option[(Int, String)] =
    def ran(ok: Boolean) = Some((if ok then 200 else 503, if ok then """{"done":true}""" else """{"error":"the run failed and changed nothing"}"""))
    def shown(xs: List[Any]) = Some((200, Json.arr(xs.map(x => Json.fromString(frflow.Example.show(x)))*).noSpaces))
    (method, path) match
      case ("POST", "/clock") =>
        io.circe.parser.parse(body).toOption.flatMap(_.hcursor.downField("advance").focus).flatMap(_.asNumber).flatMap(_.toBigInt) match
          case Some(d) => clock.advance(d); Some((200, s"""{"now":${clock.time}}"""))
          case None    => Some((400, """{"error":"advance is not a number of seconds"}"""))
      case ("POST", "/housekeep") => ran(service.housekeep())
      case ("POST", "/deliver")   => ran(service.deliver())
      case ("POST", "/faults") =>
        io.circe.parser.parse(body).toOption.flatMap(_.hcursor.downField("fail").as[List[Boolean]].toOption) match
          case Some(fs) => service.failNext(fs); Some((200, """{"done":true}"""))
          case None     => Some((400, """{"error":"fail is not a list of true and false"}"""))
      case ("GET", "/log")      => shown(service.held.log)
      case ("GET", "/outbox")   => shown(service.held.outbox)
      case ("GET", "/requests") => shown(service.held.requests)
      case ("GET", "/mailbox")  => shown(service.mailer.delivered)
      case _ => None

  def serve(port: Int, service: SharingHttp, threads: Int = 8, timeoutMs: Long = 5000,
      extra: (String, String, String) => Option[(Int, String)] = (_, _, _) => None): (HttpServer, ExecutorService) =
    val workers = Executors.newFixedThreadPool(threads)
    val server = HttpServer.create(InetSocketAddress("127.0.0.1", port), 0)
    server.setExecutor(Executors.newFixedThreadPool(threads))
    server.createContext("/", (ex: HttpExchange) =>
      val (method, path) = (ex.getRequestMethod, ex.getRequestURI.getPath)
      val rawQuery = Option(ex.getRequestURI.getRawQuery).getOrElse("")
      val (status, body) =
        try
          val input = String(ex.getRequestBody.readAllBytes(), UTF_8)
          query(rawQuery).fold((400, """{"error":"the query is not URL-encoded"}""")) { q =>
            val work = workers.submit(() => extra(method, path, input).getOrElse(answer(service, method, path, q, input)))
            try work.get(timeoutMs, TimeUnit.MILLISECONDS)
            catch case _: TimeoutException =>
              work.cancel(true)
              System.err.println(s"sharing: 503 for $method $path?$rawQuery: over $timeoutMs ms")
              (503, s"""{"error":"over $timeoutMs ms"}""")
          }
        catch case e: Throwable =>
          val cause = rootCause(e)
          System.err.println(s"sharing: 500 for $method $path?$rawQuery: ${cause.getClass.getSimpleName}: ${cause.getMessage}")
          (500, """{"error":"internal error"}""")
      val bytes = (body + "\n").getBytes(UTF_8)
      ex.getResponseHeaders.set("Content-Type", "application/json")
      ex.sendResponseHeaders(status, bytes.length)
      ex.getResponseBody.write(bytes)
      ex.close())
    server.start()
    (server, workers)

  /** The query's parameters; none when it is not URL-encoded (a stray `%`). */
  private def query(raw: String): Option[Map[String, String]] =
    scala.util.Try(raw.split("&").toList.filter(_.nonEmpty).map(_.split("=", 2) match
      case Array(k, v) => URLDecoder.decode(k, UTF_8) -> URLDecoder.decode(v, UTF_8)
      case Array(k)    => URLDecoder.decode(k, UTF_8) -> "").toMap).toOption

  private def rootCause(e: Throwable): Throwable = Option(e.getCause).filter(_ ne e).fold(e)(rootCause)

/** `sbt "sharing/runMain sharing.http.sharingServer 8091 [library.db] [--fake-clock SECONDS]"`: the service on the demo
  * library, in memory, or in a SQLite file (which starts with the demo library when it is new). On the computer's
  * clock, housekeeping runs every minute; on a fake clock starting at SECONDS, time moves and housekeeping runs only when
  * a test asks (`POST /clock`, `POST /housekeep`).
  */
object sharingServer:
  def main(args: Array[String]): Unit =
    val (opts, rest) = args.toList.span(_ != "--fake-clock")
    val fake = rest.drop(1).headOption.flatMap(a => scala.util.Try(BigInt(a)).toOption).map(FakeClock(_))
    val port = opts.headOption.flatMap(_.toIntOption).getOrElse(8091)
    val store = opts.lift(1).fold(MemoryLibraryStore(sharing.Demo.library)) { path =>
      val fresh = !java.io.File(path).exists
      val s = SqlLibraryStore.open(path)
      if fresh then s.replaceWith(sharing.Demo.library)
      s
    }
    fake match
      case Some(clock) =>
        val service = StoreHttp(store, clock)
        Server.serve(port, service, extra = Server.testing(service, clock, _, _, _))
        println(s"sharing on http://127.0.0.1:$port, on a fake clock at ${clock.time} (POST /clock, POST /housekeep)")
      case None =>
        val service = StoreHttp(store)
        Server.serve(port, service)
        Scheduler.start(service)
        println(s"sharing on http://127.0.0.1:$port (people are named in requests: there is no sign-in)")
