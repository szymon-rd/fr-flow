package auth

import cats.effect.{ExitCode, IO, Ref}
import cats.syntax.all.*
import frflow.api.{Developer, FrFlowApi, Inbox, LiveApi}
import frflow.check.Workspace
import frflow.cli.{Command, Depth, Dispatch, ReviewSession, Style, Terminal}
import frflow.protocol.{NodeId, ReviewState}
import frflow.web.Routes
import java.nio.file.{Files, Path, Paths}
import java.util.Comparator
import org.http4s.{Method, Request, Status, Uri}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** FrFlow alone on the auth example: no layer on top, none of the agent's files. The developer browses the tree, shows
  * a node, reads the status, reviews and accepts, and opens the web page; nothing of the agent is offered or written.
  */
class CoreOnlySuite extends munit.CatsEffectSuite:
  private val st = Style(color = false, unicode = false, width = None)
  private val auth = Paths.get("examples/auth").toAbsolutePath.normalize
  private def api(root: Path, env: Map[String, String] = Map("FRFLOW_KEY" -> "no.key")): IO[FrFlowApi] =
    LiveApi(knowledge, Workspace(root, "../../../lean"), env)
  private val agentFiles = List("requests.json", "conversation.json")

  /** A terminal typing `input`, keeping what is written. */
  private def terminal(input: List[String]): IO[(Terminal, IO[String])] =
    (Ref.of[IO, List[String]](input), Ref.of[IO, Vector[String]](Vector.empty)).mapN { (in, kept) =>
      val t = new Terminal:
        val interactive = true
        def out(lines: List[String]) = kept.update(_ ++ lines)
        def err(line: String) = kept.update(_ :+ s"error: $line")
        def read(prompt: String) = in.modify {
          case l :: rest => (rest, Some(l))
          case Nil => (Nil, None)
        }.flatTap(l => kept.update(_ :+ (prompt + l.getOrElse(""))))
      (t, kept.get.map(_.mkString("\n")))
    }

  private def noAgent(text: String) =
    assert(!text.toLowerCase.contains("agent") && !text.contains("[?]"), text)

  test("tree, show and status on the committed project: every node accepted, nothing waiting, no agent") {
    for
      a <- api(auth)
      (term, written) <- terminal(Nil)
      codes <- List(Command.Tree(None, json = false), Command.Show(NodeId("AccessExactly"), Depth.Normal, json = false),
        Command.Status(json = false)).traverse(Dispatch(a, term, st)(_))
      text <- written
      v <- a.view
      inbox <- a.inbox()
    yield
      // status exits 0 once Lean has proven the nodes here (`sbt leanTest` checks that); the decisions are all made
      assertEquals(codes.take(2), List(ExitCode.Success, ExitCode.Success))
      assertEquals(codes(2), Dispatch.exit(v.ok))
      List("accessExactly", "decisionContract", "Auth: 10 nodes, 10 accepted")
        .foreach(l => assert(text.contains(l), s"$l\n$text"))
      assertEquals(v.annotated.nodes.filter(_.state != ReviewState.Accepted).map(_.id), Nil)
      assertEquals((inbox.queue, inbox.aside, inbox.gone, inbox.idea), (Nil, Nil, Nil, None))
      noAgent(text)
      agentFiles.foreach(f => assert(!Files.exists(auth.resolve(".frflow").resolve(f)), f))
  }

  test("a fresh copy, reviewed from nothing: IDEA.md accepted, then the first node in the queue; signed, and nothing of the agent's written") {
    val dir = Files.createTempDirectory("frflow-core-auth")
    val copy = dir.resolve("auth")
    val env = Map("FRFLOW_KEY" -> dir.resolve("signing.key").toString)
    def copyTree(from: Path, to: Path) = Using.resource(Files.walk(from))(_.iterator.asScala.toList).foreach { p =>
      val t = to.resolve(from.relativize(p).toString)
      if Files.isDirectory(p) then Files.createDirectories(t) else Files.copy(p, t)
    }
    val typed = List("a", "it says what the service is for", "a", "a user is who a token names", "q")
    (for
      _ <- IO.blocking { copyTree(auth.resolve("src"), copy.resolve("src")); Files.copy(auth.resolve("IDEA.md"), copy.resolve("IDEA.md")) }
      a <- api(copy, env)
      before <- a.view
      (term, written) <- terminal(typed)
      code <- ReviewSession(a, term, st).run(Some("tester"))
      text <- written
      after <- a.view
      files <- IO.blocking(Using.resource(Files.walk(copy))(_.iterator.asScala.map(p => copy.relativize(p).toString).toList))
    yield
      assertEquals(code, ExitCode.Success)
      assertEquals(Inbox.of(before).idea.map(_.state), Some(ReviewState.Proposed))
      assertEquals(after.annotated.idea.map(_.state), Some(ReviewState.Accepted))
      assertEquals(after.annotated.nodes.filter(_.state == ReviewState.Accepted).map(_.id), List(NodeId("Identities")), text)
      assert(text.contains("recorded, signed by tester"), text)
      assert(text.contains("[a]ccept [r]eject [s]kip [v]iew [q]uit"), text)
      noAgent(text)
      assertEquals(files.filter(f => agentFiles.exists(f.endsWith)), Nil)
      assert(files.contains(".frflow/ledger.json"), files)
    ).guarantee(IO.blocking(Using.resource(Files.walk(dir))(_.sorted(Comparator.reverseOrder()).forEach(Files.delete(_)))))
  }

  test("the web page, with no layer: the page and its API behind the token, an empty /ext.js, no agent route") {
    val token = "t"
    for
      a <- api(auth)
      started <- a.modelFingerprint
      app = Routes(a, Developer("demo-developer"), token, started).app
      get = (path: String) => app.run(Request[IO](Method.GET, Uri.unsafeFromString(s"$path${if path.contains("?") then "&" else "?"}token=$token")))
      page <- get("/").flatMap(r => r.as[String].map(r.status -> _))
      view <- get("/api/view").map(_.status)
      ext <- get("/ext.js").flatMap(_.bodyText.compile.string)
      agent <- get("/api/agent/state").map(_.status)
    yield
      assertEquals((page._1, view), (Status.Ok, Status.Ok))
      assert(page._2.contains("FrFlow.extend") || page._2.contains("FrFlow"), page._2.take(300))
      assertEquals((ext, agent), ("", Status.NotFound))
  }
