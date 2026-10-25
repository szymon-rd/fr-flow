package sharing.http

import cats.effect.SyncIO
import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.{InetSocketAddress, URLDecoder}
import java.nio.charset.StandardCharsets.UTF_8
import java.util.concurrent.{ExecutorService, Executors, TimeUnit, TimeoutException}
import sharing.knowledge
import sharing.store.{LibraryStore, MemoryLibraryStore, SqlLibraryStore}

/** The service on a store: HandleContract's proven flow, run on it, one request at a time (each reads the library the
  * last one left).
  */
final class StoreHttp(s: LibraryStore) extends SharingHttp:
  private val run = knowledge.run[SyncIO](SharingHttp.handleContract)(LibraryStore.store.bind(s))
  def handle(request: Request): Answer = synchronized(run(request).unsafeRunSync())

/** The service over HTTP on localhost. Requests run on a pool of workers, each with a time limit (503 past it); an
  * internal error is answered 500 and logged with the request, never a dropped connection. ServerWiring governs it.
  */
object Server:
  // Answers go out as written: without it, a small answer waits on the client's delayed ACK (about 40 ms).
  System.setProperty("sun.net.httpserver.nodelay", "true")

  /** One request answered: what the server sends, and what the tests call without a socket. */
  def answer(service: SharingHttp, method: String, path: String, query: Map[String, String], body: String): (Int, String) =
    val (status, json) = HttpCodec.request(method, path, query, body).fold(HttpCodec.reply, r => HttpCodec.reply(service.handle(r)))
    (status, json.noSpaces)

  def serve(port: Int, service: SharingHttp, threads: Int = 8, timeoutMs: Long = 5000): (HttpServer, ExecutorService) =
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
            val work = workers.submit(() => answer(service, method, path, q, input))
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

/** `sbt "sharing/runMain sharing.http.sharingServer 8091 [library.db]"`: the service on the demo library, in memory, or
  * in a SQLite file (which starts with the demo library when it is new).
  */
object sharingServer:
  def main(args: Array[String]): Unit =
    val port = args.headOption.flatMap(_.toIntOption).getOrElse(8091)
    val store = args.lift(1).fold(MemoryLibraryStore(sharing.Demo.library)) { path =>
      val fresh = !java.io.File(path).exists
      val s = SqlLibraryStore.open(path)
      if fresh then s.replaceWith(sharing.Demo.library)
      s
    }
    Server.serve(port, StoreHttp(store))
    println(s"sharing on http://127.0.0.1:$port (people are named in requests: there is no sign-in)")
