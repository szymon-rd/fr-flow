package rebac

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.{InetSocketAddress, URLDecoder}
import java.nio.charset.StandardCharsets.UTF_8

/** The service over HTTP, on localhost: a thin layer over RebacService and TupleSyntax.
  *   GET  /check?tuple=doc:readme#viewer@user:ann[&at=V]  → yes or no
  *   POST /write?tuple=…  and  POST /delete?tuple=…       → the new version
  * ServiceWiring governs this file.
  */
object RebacHttp:
  /** The status and body answering one request. */
  def answer(service: RebacService, method: String, path: String, params: Map[String, String]): (Int, String) =
    val tuple = params.get("tuple").toRight("give a tuple: ?tuple=doc:readme#viewer@user:ann").flatMap(TupleSyntax.parse)
    (method, path) match
      case ("GET", "/check") =>
        tuple match
          case Right(RelTuple(o, r, Subject.Person(p))) =>
            (200, if service.check(Query(o, r, p), params.get("at").flatMap(_.toIntOption)) then "yes" else "no")
          case Right(_)  => (400, "a check names a person: doc:readme#viewer@user:ann")
          case Left(why) => (400, why)
      case ("POST", "/write" | "/delete") =>
        tuple.fold(why => (400, why), t => (200, service.write(if path == "/write" then Write.Add(t) else Write.Remove(t)).toString))
      case _ => (404, "GET /check, POST /write, POST /delete")

  def serve(port: Int, service: RebacService): HttpServer =
    val server = HttpServer.create(InetSocketAddress("127.0.0.1", port), 0)
    server.createContext("/", (ex: HttpExchange) =>
      val params = Option(ex.getRequestURI.getRawQuery).toList.flatMap(_.split("&")).flatMap(_.split("=", 2) match
        case Array(k, v) => Some(k -> URLDecoder.decode(v, UTF_8))
        case _           => None).toMap
      val (code, body) = answer(service, ex.getRequestMethod, ex.getRequestURI.getPath, params)
      val bytes = (body + "\n").getBytes(UTF_8)
      ex.sendResponseHeaders(code, bytes.length)
      ex.getResponseBody.write(bytes)
      ex.close())
    server.start()
    server

/** `sbt "rebac/runMain rebac.rebacServer 8090"`: the service with the demo schema and OpenFGA's depth. */
object rebacServer:
  def main(args: Array[String]): Unit =
    val port = args.headOption.flatMap(_.toIntOption).getOrElse(8090)
    RebacHttp.serve(port, RebacService(demoSchema, serviceLevels))
    println(s"rebac on http://127.0.0.1:$port")
