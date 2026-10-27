package frflow.agent

import cats.effect.IO
import frflow.agent.work.AgentApi
import frflow.api.Opened
import frflow.cli.Cli
import frflow.web.{Gate, Routes}
import io.circe.Json
import io.circe.syntax.*
import org.http4s.circe.CirceEntityCodec.*
import org.http4s.{Header, Method, Request, Status, Uri}
import org.typelevel.ci.CIString

/** The agent layer in the web view: its routes behind the page's token, the developer asking and closing. */
class AgentWebSuite extends munit.CatsEffectSuite:
  private def req(method: Method, path: String) = Request[IO](method, Uri.unsafeFromString(path))
    .putHeaders(Header.Raw(CIString(Routes.TokenHeader), "t"))

  test("ask and close go through the agent layer as the developer; its state carries requests, questions and the " +
    "nodes with it") {
    for
      api     <- Opened.api(Opened.before)
      a       <- AgentApi.inMemory[IO](api)
      part    <- AgentLayer(_ => IO.pure(a)).part(Cli.host(api), "ann")
      app     <- api.reading.modelFingerprint.map(f => Routes(api, "ann", Gate("t", f), List(part)).app)
      asked   <- app.run(req(Method.POST, "/api/agent/ask").withEntity(Json.obj("node" -> "nonNegative".asJson,
                   "text" -> "name the number plainly".asJson))).flatMap(_.as[Json])
      _       <- a.asked("Can a number be negative?", "No, never.")
      state   <- app.run(req(Method.GET, "/api/agent/state")).flatMap(_.as[Json])
      id       = asked.hcursor.get[String]("id").getOrElse("")
      closed  <- app.run(req(Method.POST, "/api/agent/close").withEntity(List(id).asJson)).map(_.status)
      unknown <- app.run(req(Method.POST, "/api/agent/close").withEntity(List("R0").asJson)).map(_.status)
      script  <- app.run(req(Method.GET, "/ext.js")).flatMap(_.bodyText.compile.string)
    yield
      assertEquals(asked.hcursor.downField("asked").get[String]("by"), Right("ann"))
      assertEquals(state.hcursor.get[List[String]]("withAgent"), Right(List("nonNegative")))
      assertEquals(state.hcursor.downField("questions").downArray.get[String]("assumed"), Right("No, never."))
      assertEquals((closed, unknown), (Status.Ok, Status.NotFound))
      assert(script.contains("FrFlow.extend") || script.contains("F.extend"), script.take(200))
  }
