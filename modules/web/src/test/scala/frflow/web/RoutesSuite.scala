package frflow.web

import cats.effect.IO
import cats.syntax.all.*
import frflow.api.*
import frflow.protocol.*
import io.circe.Json
import io.circe.syntax.*
import org.http4s.{Header, Method, Request as Http, Status, Uri}
import org.http4s.circe.CirceEntityCodec.*
import org.typelevel.ci.CIString

/** The routes in memory, over the fake API: no port, no files. */
class RoutesSuite extends munit.CatsEffectSuite:
  private val token = "the-token"
  private val dev = Developer("dev")
  private def routes(api: FakeApi) = api.modelFingerprint.map(Routes(api, dev, token, _).app)
  private def call(api: FakeApi, method: Method, path: String, body: Option[Json] = None, as: String = token) =
    val req = Http[IO](method, Uri.unsafeFromString(path)).putHeaders(Header.Raw(CIString(Routes.TokenHeader), as))
    routes(api).flatMap(_.run(body.fold(req)(req.withEntity(_))))
  private def json(api: FakeApi, method: Method, path: String, body: Option[Json] = None) =
    call(api, method, path, body).flatMap(r => r.as[Json].map(r.status -> _))
  private def accept(reason: String) = (Decide.Accept(List(NodeId("Decide")), reason): Decide).asJson

  test("without the token, or with another, every route is refused, the page too") {
    for
      api <- FakeApi()
      app <- routes(api)
      none <- app.run(Http[IO](Method.GET, Uri.unsafeFromString("/api/view")))
      wrong <- call(api, Method.GET, "/api/view", as = "guess")
      page <- call(api, Method.GET, "/", as = "guess")
      decide <- call(api, Method.POST, "/api/decide", Some(accept("the token's user is admitted")), as = "guess")
      ledger <- api.ledgerNow
      inQuery <- app.run(Http[IO](Method.GET, Uri.unsafeFromString(s"/?token=$token")))
    yield
      assertEquals(List(none, wrong, page, decide).map(_.status), List.fill(4)(Status.Forbidden))
      assertEquals(ledger, Sample.ledgerNow)
      assertEquals(inQuery.status, Status.Ok)
  }

  test("view, tree, inbox and details return the API's values as its codecs write them") {
    for
      api <- FakeApi()
      view <- json(api, Method.GET, "/api/view")
      tree <- json(api, Method.GET, "/api/tree")
      inbox <- json(api, Method.GET, "/api/inbox")
      details <- json(api, Method.GET, "/api/details/Decide")
      unknown <- json(api, Method.GET, "/api/details/Nope")
      expected <- (api.view, api.tree(None), api.inbox, api.details(NodeId("Decide"))).tupled
    yield
      assertEquals(List(view, tree, inbox, details),
        List(expected._1.asJson, expected._2.asJson, expected._3.asJson, expected._4.asJson).map(Status.Ok -> _))
      assertEquals(unknown, Status.NotFound -> Json.obj("error" -> "unknown node Nope".asJson))
  }

  test("decide records through the API's decide; a refusal is a 409 with its message, and records nothing") {
    for
      api <- FakeApi()
      short <- json(api, Method.POST, "/api/decide", Some(accept("fine")))
      notProposal <- json(api, Method.POST, "/api/decide", Some((Decide.Reject(NodeId("Decide"), "a user is not a token"): Decide).asJson))
      unchanged <- api.ledgerNow
      done <- json(api, Method.POST, "/api/decide", Some(accept("the token's user is the one admitted")))
      after <- api.ledgerNow
      bad <- json(api, Method.POST, "/api/decide", Some(Json.obj("Accept" -> Json.obj())))
    yield
      assertEquals(short, Status.Conflict -> Json.obj("error" -> Refusal.NoReason.message.asJson))
      assertEquals(notProposal._1, Status.Conflict)
      assertEquals(unchanged, Sample.ledgerNow)
      assertEquals(done._1, Status.Ok)
      assertEquals(after.current(NodeId("Decide")).map(d => (d.action, d.by, d.reason)),
        Some((Action.Accept, dev.name, "the token's user is the one admitted")))
      assertEquals(done._2.hcursor.downField("decisions").downN(0).get[String]("node"), Right("Decide"))
      assertEquals(bad._1, Status.BadRequest)
  }

  test("once the model's sources change, the page is told, and deciding is refused until serve restarts") {
    for
      api <- FakeApi()
      app <- routes(api)
      _ <- api.editModel
      req = (p: String) => Http[IO](Method.GET, Uri.unsafeFromString(p)).putHeaders(Header.Raw(CIString(Routes.TokenHeader), token))
      serving <- app.run(req("/api/serving")).flatMap(_.as[Serving])
      refused <- app.run(req("/api/decide").withMethod(Method.POST).withEntity(accept("the token's user is the one admitted")))
      message <- refused.as[Json]
      ledger <- api.ledgerNow
    yield
      assertEquals(serving, Serving(dev.name, modelChanged = true))
      assertEquals((refused.status, message), (Status.Conflict, Json.obj("error" -> Routes.ModelChanged.asJson)))
      assertEquals(ledger, Sample.ledgerNow)
  }

  test("ask and close go through the API as the developer") {
    for
      api <- FakeApi()
      asked <- json(api, Method.POST, "/api/ask", Some(Asking(Some(NodeId("Decide")), "Name the user.").asJson))
      empty <- json(api, Method.POST, "/api/close", Some(List(RequestId("R9")).asJson))
      closed <- json(api, Method.POST, "/api/close", Some(List(RequestId("R1")).asJson))
      v <- api.view
    yield
      assertEquals(asked._1, Status.Ok)
      assertEquals(empty._1, Status.NotFound)
      assertEquals(closed._1, Status.Ok)
      assert(v.requests.exists(q => q.text == "Name the user." && q.by == dev.name && q.node.contains(NodeId("Decide"))), v.requests)
      assertEquals(v.requests.find(_.id == RequestId("R1")).map(_.status), Some(RequestStatus.Closed))
  }

  test("the inbox carries IDEA.md and the agent's open questions; the page accepts IDEA.md as it saw it") {
    val talk = Conversation(questions = List(Question("Q1", "Can a token be shared?", "No: one user per token.", Sample.at)))
    for
      api <- FakeApi(Sample.snapshot.copy(idea = "# Auth\n\nOnly the authorized get in.\n"), Sample.ledgerNow, Nil, talk)
      inbox <- json(api, Method.GET, "/api/inbox")
      version = inbox._2.hcursor.downField("idea").downField("version").as[String].toOption.get
      stale <- json(api, Method.POST, "/api/decide", Some((Decide.Accept(List(IdeaReview.Id), "says what it is for", Nil, Map(IdeaReview.Id -> Version("old"))): Decide).asJson))
      accepted <- json(api, Method.POST, "/api/decide", Some((Decide.Accept(List(IdeaReview.Id), "says what it is for", Nil, Map(IdeaReview.Id -> Version(version))): Decide).asJson))
      v <- api.view
    yield
      assertEquals(inbox._2.hcursor.downField("idea").downField("text").as[String], Right("# Auth\n\nOnly the authorized get in.\n"))
      assertEquals(inbox._2.hcursor.downField("questions").downN(0).downField("id").as[String], Right("Q1"))
      assertEquals((stale._1, accepted._1), (Status.Conflict, Status.Ok))
      assertEquals(v.annotated.idea.map(_.state), Some(ReviewState.Accepted))
  }
