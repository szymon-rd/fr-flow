package frflow.agent

import cats.effect.IO
import frflow.agent.conversation.*
import frflow.agent.panel.*
import frflow.agent.request.*
import frflow.api.*
import frflow.check.TempDirs
import frflow.ledger.JsonStore
import frflow.protocol.*
import frflow.web.Routes
import io.circe.Json
import io.circe.syntax.*
import org.http4s.{Header, Method, Request as Http, Status, Uri}
import org.http4s.circe.CirceEntityCodec.*
import org.typelevel.ci.CIString

/** The agent layer in the web view: its routes behind the page's token, its script served with the page's. */
class AgentWebSuite extends munit.CatsEffectSuite with TempDirs:
  private val token = "the-token"
  private val dev = Developer("dev")
  private def app(talk: Conversation = Conversation.empty) =
    val dir = tempDir("frflow-agent-web")
    for
      api <- FakeApi()
      _ <- JsonStore.make(AgentApi.conversationFile(dir), Conversation.empty).flatMap(_.update[Nothing, Unit](_ => Right((talk, ()))))
      host = Host(api, dir, Map.empty)
      part <- Agent.part(host, dev)
      started <- api.modelFingerprint
    yield (Routes(api, dev, token, started, List(part)).app, host)
  private def call(a: org.http4s.HttpApp[IO], method: Method, path: String, body: Option[Json] = None) =
    val req = Http[IO](method, Uri.unsafeFromString(path)).putHeaders(Header.Raw(CIString(Routes.TokenHeader), token))
    a.run(body.fold(req)(req.withEntity(_))).flatMap(r => r.as[Json].map(r.status -> _))

  test("ask and close go through the agent layer as the developer; its state carries requests, questions and the nodes with it") {
    val talk = Conversation(questions = List(Question("Q1", "Can a token be shared?", "No: one user per token.", Sample.at)))
    for
      (a, host) <- app(talk)
      asked <- call(a, Method.POST, "/api/agent/ask", Some(Asking(Some(NodeId("Decide")), "Name the user.").asJson))
      unknown <- call(a, Method.POST, "/api/agent/close", Some(List(RequestId("R9")).asJson))
      state <- call(a, Method.GET, "/api/agent/state")
      id = asked._2.hcursor.get[String]("id").toOption.get
      closed <- call(a, Method.POST, "/api/agent/close", Some(List(RequestId(id)).asJson))
      script <- a.run(Http[IO](Method.GET, Uri.unsafeFromString(s"/ext.js?token=$token"))).flatMap(_.bodyText.compile.string)
    yield
      assertEquals((asked._1, unknown._1, closed._1), (Status.Ok, Status.NotFound, Status.Ok))
      val s = state._2.as[AgentState].toOption.get
      assertEquals(s.requests.map(q => (q.node, q.text, q.by)), List((Some(NodeId("Decide")), "Name the user.", dev.name)))
      assertEquals((s.withAgent, s.questions.map(_.id)), (List(NodeId("Decide")), List("Q1")))
      assert(script.contains("F.extend("), script.take(200))
  }
