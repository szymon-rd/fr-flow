package rebac

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.{InetSocketAddress, URLDecoder}
import java.nio.charset.StandardCharsets.UTF_8
import java.util.concurrent.{Executors, TimeUnit, TimeoutException}

/** The service over HTTP, on localhost: routes to requests, HttpLayer to replies, replies to text.
  *   GET  /check?tuple=doc:readme#viewer@user:ann[&at=V]  → yes or no; the version in the Rebac-Version header
  *   POST /write?tuple=…  and  POST /delete?tuple=…       → the new version
  * A refusal is 400 with the reason; an unknown path 404; a request over its time 503; an internal error (a contract
  * the running code broke) 500, logged with the request. ServiceWiring governs this file.
  */
object RebacHttp:
  /** The request a method, path and parameters make. */
  def route(method: String, path: String, params: Map[String, String]): Request =
    val tuple = params.get("tuple").fold(Given.Missing)(t => TupleSyntax.parse(t).fold(Given.Malformed(_), Given.Tuple(_)))
    (method, path) match
      case ("GET", "/check")   => Request.Check(tuple, params.get("at").fold(At.Latest)(a => a.toIntOption.fold(At.Invalid(a))(At.Version(_))))
      case ("POST", "/write")  => Request.Add(tuple)
      case ("POST", "/delete") => Request.Delete(tuple)
      case _                   => Request.Unknown(method, path)

  /** The status, body and headers of a reply. */
  def render(layer: HttpLayer, r: Request, reply: Reply): (Int, String, Map[String, String]) =
    val version = Map("Rebac-Version" -> reply.version.toString)
    (reply.status, reply.answer) match
      case (200, Some(a)) => (200, if a then "yes" else "no", version)
      case (200, None)    => (200, reply.version.toString, version)
      case (status, _)    => (status, layer.explain(r), version)

  /** One request, answered: what the server sends, and what tests call without a socket. */
  def answer(layer: HttpLayer, method: String, path: String, params: Map[String, String]): (Int, String, Map[String, String]) =
    val r = route(method, path, params)
    render(layer, r, layer.respond(r))

  /** The server: requests run on `threads` workers, each given `timeoutMs`. */
  def serve(port: Int, backend: Backend, threads: Int = 8, timeoutMs: Long = 10000): HttpServer =
    val layer = HttpLayer(backend)
    val workers = Executors.newFixedThreadPool(threads)
    val server = HttpServer.create(InetSocketAddress("127.0.0.1", port), 0)
    server.setExecutor(Executors.newFixedThreadPool(threads))
    server.createContext("/", (ex: HttpExchange) =>
      val (method, path, query) = (ex.getRequestMethod, ex.getRequestURI.getPath, Option(ex.getRequestURI.getRawQuery).getOrElse(""))
      val (code, body, headers) =
        try parse(query) match
          case None => (400, "the query is not URL-encoded text", Map.empty[String, String])
          case Some(params) =>
            val work = workers.submit(() => answer(layer, method, path, params))
            try work.get(timeoutMs, TimeUnit.MILLISECONDS)
            catch
              case _: TimeoutException =>
                work.cancel(true)
                System.err.println(s"rebac: 503 for $method $path?$query: over $timeoutMs ms")
                (503, s"the request took longer than $timeoutMs ms", Map.empty[String, String])
        catch case e: Throwable =>
          val cause = rootCause(e)
          System.err.println(s"rebac: 500 for $method $path?$query: ${cause.getClass.getSimpleName}: ${cause.getMessage}")
          (500, s"internal error: ${cause.getMessage}", Map.empty)
      val bytes = (body + "\n").getBytes(UTF_8)
      headers.foreach((k, v) => ex.getResponseHeaders.set(k, v))
      ex.sendResponseHeaders(code, bytes.length)
      ex.getResponseBody.write(bytes)
      ex.close())
    server.start()
    server

  /** The query's parameters; none when it is not URL-encoded text (a stray `%`). */
  private def parse(query: String): Option[Map[String, String]] =
    scala.util.Try(query.split("&").toList.filter(_.nonEmpty).flatMap(_.split("=", 2) match
      case Array(k, v) => Some(k -> URLDecoder.decode(v, UTF_8))
      case _           => None).toMap).toOption

  private def rootCause(e: Throwable): Throwable =
    Option(e.getCause).filter(_ ne e).fold(e)(rootCause)

/** `sbt "rebac/runMain rebac.rebacServer 8090"`: the service with the demo schema and OpenFGA's depth. */
object rebacServer:
  def main(args: Array[String]): Unit =
    val port = args.headOption.flatMap(_.toIntOption).getOrElse(8090)
    RebacHttp.serve(port, RebacService(demoSchema, serviceLevels))
    println(s"rebac on http://127.0.0.1:$port")
    println("rebac: writes are not authenticated, and tuples are kept in memory only: a restart starts empty (see examples/rebac/README.md)")
