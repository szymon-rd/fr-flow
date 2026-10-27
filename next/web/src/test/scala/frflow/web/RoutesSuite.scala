package frflow.web

import cats.effect.IO
import cats.syntax.all.*
import frflow.api.{FrFlowApi, Opened}
import frflow.core.name.RelPath
import io.circe.Json
import io.circe.syntax.*
import org.http4s.circe.CirceEntityCodec.*
import org.http4s.dsl.io.*
import org.http4s.implicits.*
import org.http4s.{Header, HttpRoutes, Method, Request, Status, Uri}
import org.typelevel.ci.CIString

/** The web view's routes over the API in memory, behind the session's token. */
class RoutesSuite extends munit.CatsEffectSuite:
  private val token = "t0k3n"
  private def routes(api: FrFlowApi[IO], parts: List[WebPart] = Nil) =
    api.reading.modelFingerprint.map(f => Routes(api, "ann", Gate(token, f), parts).app)
  private def get(path: String, tok: Option[String] = Some(token)) =
    Request[IO](Method.GET, Uri.unsafeFromString(path)).putHeaders(tok.toList.map(Header.Raw(CIString(Routes
      .TokenHeader), _)))
  private def post(path: String, body: Json) = get(path).withMethod(Method.POST).withEntity(body)
  private val accept = Json.obj("action" -> "accept".asJson, "nodes" -> List("nonNegative").asJson,
    "reason" -> "it says what the service must do".asJson)

  test("without the token, or with another, every route is refused, the page too") {
    for
      app   <- Opened.api(Opened.before).flatMap(routes(_))
      codes <- List(get("/", None), get("/api/view", None), get("/api/view", Some("other")), post("/api/decide", accept)
                 .removeHeader(CIString(Routes.TokenHeader))).traverse(app.run(_).map(_.status))
      query <- app.run(Request[IO](Method.GET, uri"/api/view".withQueryParam("token", token))).map(_.status)
    yield
      assertEquals(codes.distinct, List(Status.Forbidden))
      assertEquals(query, Status.Ok)
  }

  test("view, tree, inbox and diff return the views as JSON, each case naming its type") {
    for
      app   <- Opened.api(Opened.before).flatMap(routes(_))
      view  <- app.run(get("/api/view")).flatMap(_.as[Json])
      tree  <- app.run(get("/api/tree")).flatMap(_.as[Json])
      inbox <- app.run(get("/api/inbox")).flatMap(_.as[Json])
      diff  <- app.run(get("/api/diff/nonNegative")).flatMap(_.as[Json])
      none  <- app.run(get("/api/diff/nope")).map(_.status)
    yield
      val first = view.hcursor.downField("nodes").downArray
      assertEquals(first.get[String]("id"), Right("nonNegative"))
      assertEquals(first.downField("review").downField("standing").downField("state").get[String]("type"),
        Right("Proposed"))
      assertEquals(tree.hcursor.downArray.get[String]("node"), Right("nonNegative"))
      assertEquals(inbox.as[List[String]], Right(List("nonNegative", "sameAbove")))
      assert(diff.hcursor.downField("fields").focus.isDefined, diff.noSpaces)
      assertEquals(none, Status.NotFound)
  }

  test("decide records through the API's decide; a refusal is a 409 naming it, and records nothing") {
    val first = Json.obj("action" -> "accept".asJson, "nodes" -> List("sameAbove").asJson,
      "reason" -> "it says what the service must do".asJson)
    for
      api      <- Opened.api(Opened.before)
      app      <- routes(api)
      refused  <- app.run(post("/api/decide", first))
      body     <- refused.as[Json]
      done     <- app.run(post("/api/decide", accept))
      recorded <- done.as[Json]
      view     <- api.reading.view
    yield
      assertEquals(refused.status, Status.Conflict)
      assertEquals(body.hcursor.downField("refusal").get[String]("type"), Right("AcceptFirst"))
      assertEquals(done.status, Status.Ok)
      assertEquals(recorded.hcursor.downField("recorded").downArray.get[String]("node"), Right("nonNegative"))
      assertEquals(view.node(frflow.core.name.NodeId("nonNegative")).flatMap(_.review.decisions.binding).map(_.author.by),
        Some("ann"))
  }

  test("once the model's sources change, the page is told, and deciding is refused until serve restarts") {
    val file = RelPath.fromIdentifiers("src/main", "Shelf.scala")
    for
      ports   <- Opened.ports(Map(file -> "object Shelf"))
      app     <- Opened.over(Opened.before, ports).flatMap(routes(_))
      before  <- app.run(get("/api/serving")).flatMap(_.as[Json])
      _       <- ports.files.writeIfChanged(file, "object Shelf { val more = 1 }")
      after   <- app.run(get("/api/serving")).flatMap(_.as[Json])
      decided <- app.run(post("/api/decide", accept)).map(_.status)
    yield
      assertEquals(before.hcursor.get[Boolean]("modelChanged"), Right(false))
      assertEquals(after.hcursor.get[Boolean]("modelChanged"), Right(true))
      assertEquals(decided, Status.Conflict)
  }

  test("a layer on top adds routes, behind the same token, and its script, served as /ext.js (empty with none)") {
    val part = WebPart(HttpRoutes.of[IO] { case GET -> Root / "api" / "layer" / "hello" => Ok("hi") }, "FrFlow;")
    for
      api    <- Opened.api(Opened.before)
      plain  <- routes(api)
      layer  <- routes(api, List(part))
      hello  <- layer.run(get("/api/layer/hello")).flatMap(_.as[String])
      denied <- layer.run(get("/api/layer/hello", None)).map(_.status)
      script <- layer.run(get("/ext.js")).flatMap(_.bodyText.compile.string)
      none   <- plain.run(get("/ext.js")).flatMap(_.bodyText.compile.string)
    yield
      assertEquals((hello, denied, script, none), ("hi", Status.Forbidden, "FrFlow;", ""))
  }
