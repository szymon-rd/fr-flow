package frflow.api

import cats.effect.IO
import frflow.{KnowledgeBase, Node}
import frflow.check.*
import frflow.lean.Generate
import frflow.ledger.*
import frflow.protocol.*
import io.circe.syntax.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.time.Instant
import scala.jdk.CollectionConverters.*

/** The API over a project on disk: today's `Workflow` (render, check, the snapshot, context, scaffold)
  * and the ledger's stores and signing. Thin on purpose: what it computes is in this package's pure
  * objects, so a change of the check or ledger modules' signatures is a change here only.
  *
  * @param keyFile the developer's signing key (see `LiveApi.keyFile`); read only to decide or sign
  */
final class LiveApi private (kb: KnowledgeBase, ws: Workspace, keyFile: Path, env: Map[String, String]) extends FrFlowApi:
  private val workflow = Workflow(kb, ws)
  private val keys = ws.root.resolve(".frflow/keys")

  def view: IO[View] = IO.blocking(viewNow)

  private def viewNow: View =
    val ledger = workflow.ledger
    val a = Decisions.annotate(workflow.baseSnapshot, ledger)
    View(a, workflow.allRequests, unsigned(ledger), Signing.warnings(ws.ledgerFile, ledger) ++ a.snapshot.warnings)

  private def unsigned(l: Ledger) = Signing.unsigned(l, keys).map((id, d) => Unsigned(id, Ledger.entry(d), d))

  def codeChange(r: Reviewed): IO[Option[CodeChange]] = IO.blocking {
    r.node.code.flatMap { c =>
      if r.state == ReviewState.Proposed then
        Some(CodeChange(c.files, c.files.map(ws.root.resolve).filter(Files.isRegularFile(_))
          .map(p => s"--- ${ws.root.relativize(p)} (in full)\n${Files.readString(p, UTF_8)}").mkString("\n"), inFull = true))
      else Option.when(r.review.causes.contains(Cause.Code))(Details.binding(r)).flatten.map { d =>
        val since = d.tree.filter(Git.has(ws.root, _)).orElse(d.commit).getOrElse("")
        CodeChange(c.files, Git.diff(ws.root, since, c.files), inFull = false)
      }
    }
  }

  def history: IO[List[Logged]] = IO.blocking(workflow.ledger.all.map(Logged.apply))

  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]] = IO.blocking {
    val (v, before) = (viewNow, workflow.ledger)
    Deciding(v, before, d, by, Deciding.At(Instant.now.toString)).map(Deciding.added(v, before, _))
  }

  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]] = IO.blocking {
    Store.locked(ws.ledgerFile) {
      val (v, before) = (viewNow, workflow.ledger)
      val files = v.snapshot.nodes.flatMap(_.code).flatMap(_.files).distinct
      def known(s: String) = Option(s).filter(_.nonEmpty)
      val at = Deciding.At(Instant.now.toString, known(Git.head(ws.root)), known(Git.snapshot(ws.root, files)))
      Deciding(v, before, d, by, at).map { after =>
        val (priv, pub) = key(by)
        val signed = Signing.signNew(before, after, priv, pub)
        LedgerStore.save(ws.ledgerFile, signed)
        Deciding.added(v, before, signed)
      }
    }
  }

  /** The developer's key, its public key filed under their name on first use. */
  private def key(by: Developer) =
    val (priv, pub) = Signing.loadOrCreate(keyFile)
    Signing.publish(pub, keys, by.name)
    (priv, pub)

  def sign(entries: Option[Set[EntryRef]], by: Developer): IO[Either[Refusal, List[Unsigned]]] = IO.blocking {
    Store.locked(ws.ledgerFile) {
      val l = workflow.ledger
      val all = unsigned(l)
      val chosen = entries.fold(all)(es => all.filter(u => es(u.entry)))
      val missing = entries.fold(Set.empty[EntryRef])(_ -- all.map(_.entry))
      if missing.nonEmpty then Left(Refusal(s"not a decision waiting to be signed: ${missing.mkString(", ")}"))
      else if chosen.isEmpty then Left(Refusal("every decision is signed"))
      else
        val (priv, pub) = key(by)
        LedgerStore.save(ws.ledgerFile, Signing.signEntries(l, chosen.map(_.entry).toSet, priv, pub))
        Right(chosen)
    }
  }

  def developer(as: Option[String]): IO[Either[Refusal, Developer]] = IO.blocking {
    as.orElse(env.get("FRFLOW_AS")).map(_.trim).filter(_.nonEmpty).orElse(keyName).map(Developer.apply)
      .toRight(Refusal("say who decides: --as NAME (your key's public half is filed as .frflow/keys/NAME.pub)"))
  }

  /** The name the developer's public key is filed under in `.frflow/keys`, if it is. */
  private def keyName: Option[String] =
    Option.when(Files.isRegularFile(keyFile) && Files.isDirectory(keys)) {
      val pub = java.util.Base64.getEncoder.encodeToString(Signing.loadOrCreate(keyFile)._2.getEncoded)
      scala.util.Using.resource(Files.list(keys))(_.iterator.asScala.toList).sortBy(_.toString)
        .find(f => f.toString.endsWith(".pub") && Files.readString(f, UTF_8).trim == pub)
        .map(_.getFileName.toString.stripSuffix(".pub"))
    }.flatten

  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[Refusal, Request]] = IO.blocking {
    val seen = node.flatMap(id => viewNow.node(id)).map(_.review.version)
    if text.trim.isEmpty then Left(Refusal("say what to change"))
    else if node.exists(id => kb.node(id.value).isEmpty) then Left(Refusal(s"unknown node ${node.fold("")(_.value)}"))
    else Store.locked(ws.requestsFile) {
      val rs = RequestStore.load(ws.requestsFile)
      val now = Instant.now
      val id = Iterator.from(0).map(k => RequestId(s"R${java.lang.Long.toString(now.toEpochMilli + k, 36)}")).find(i => !rs.exists(_.id == i))
      val r = Request(id.getOrElse(RequestId("R")), node, text.trim, by.name, now.toString.take(19) + "Z", RequestStatus.Open, seen = seen)
      saveRequests(rs :+ r)
      Right(r)
    }
  }

  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]] = IO.blocking {
    Store.locked(ws.requestsFile) {
      val rs = RequestStore.load(ws.requestsFile)
      ids.filterNot(i => rs.exists(_.id == i)) match
        case Nil =>
          val closed = rs.map(r => if ids.contains(r.id) then r.copy(status = RequestStatus.Closed) else r)
          saveRequests(closed)
          Right(closed.filter(r => ids.contains(r.id)))
        case unknown => Left(Refusal(s"no request ${unknown.mkString(", ")}"))
    }
  }

  private def saveRequests(rs: List[Request]) = Store.write(ws.requestsFile, Canonical.file(rs.asJson) + "\n")

  def answer(to: String, text: String): IO[Either[Refusal, RequestId]] = IO.blocking {
    RequestStore.answer(ws.requestsFile, to, text, kb.node(_).isDefined, Instant.now).left.map(Refusal.apply)
  }

  def render: IO[Rendered] = IO.blocking {
    val changed = workflow.render()
    Rendered(changed, ws.root.relativize(workflow.writeSnapshot()).toString)
  }

  def check(node: Option[NodeId]): IO[CheckReport] =
    lean *> node.fold(IO.unit)(id => this.node(id).void) *> IO.blocking {
      val results = workflow.check(node.map(_.value))
      workflow.writeSnapshot()
      CheckReport(results.map(checked), statusNow)
    }

  def status: IO[StatusReport] = IO.blocking { workflow.writeSnapshot(); statusNow }

  def ci: IO[CiReport] = lean *> IO.blocking {
    val results = workflow.check()
    CiReport(results.filter(_._2.status != CheckStatus.Proven).map(checked), statusNow)
  }

  def context(id: NodeId): IO[ContextDoc] = node(id).flatMap(n => IO.blocking(ContextDoc(id, workflow.context(n))))

  def scaffold(id: NodeId): IO[Scaffolded] = node(id).flatMap { n =>
    IO.blocking {
      val created = workflow.scaffold(n)
      workflow.writeSnapshot()
      Scaffolded(id, Option.when(created)(s"lean/${workflow.generate.proofsPath(n.id)}"))
    }
  }

  private def node(id: NodeId): IO[Node[?]] =
    IO.fromOption(kb.node(id.value))(FrFlowError.UnknownNode(id.value))

  private def lean: IO[Unit] = IO.blocking(Lake(ws.lean).available).ifM(IO.unit, IO.raiseError(FrFlowError.LeanMissing))

  private def statusNow: StatusReport =
    val v = viewNow
    val probes = kb.nodes.flatMap(workflow.current).flatMap(_.obligations)
      .count(o => o.name.startsWith("probe") && o.status == ObligationStatus.Proven)
    StatusReport(v, Proofs.coverage(v.snapshot, probes), notes, Reports.complete(v.annotated) && v.warnings.isEmpty)

  /** What each invariant does not reach (by the type of what a contract returns), so a gap is seen. */
  private def notes: List[String] = kb.nodes.filter(_.isInvariant).flatMap { i =>
    val out = kb.nodes.filter(c => c.kind == frflow.NodeKind.Contract && !kb.inScope(i).contains(c))
    Option.when(out.nonEmpty)(s"${i.id} does not reach ${out.map(c => s"${c.id} (returns ${c.post.flatMap(_.params.lastOption).fold("?")(_._2)})").mkString(", ")}: its rule is about none of what they return")
  }

  /** One node as `check` left it (see `CheckedNode`). */
  private def checked(n: Node[?], c: NodeCheck): CheckedNode =
    val failing = kb.exampleResults(n).filter(r => r.contract != "ok" || r.implementation.exists(_ != "ok"))
      .map(r => FailingExample(r.example.describe, r.verdict))
    CheckedNode(NodeId(n.id), c.status,
      notProven = c.obligations.filter(r => !r.isEvaluation && !r.fine).map(_.name),
      problems = c.obligations.filterNot(_.fine),
      failing = failing,
      idle = c.obligations.find(r => r.name == "idle" && r.status == ObligationStatus.Idle).map(_.detail),
      // With an example failing the node may be false: no hint to prove it.
      messages = c.messages.filterNot(m => failing.nonEmpty && m.startsWith("prove it in")))

object LiveApi:
  /** The API over the project at `ws`; the model's problems, if any, fail it (nothing else is computed). */
  def apply(kb: KnowledgeBase, ws: Workspace, keyFile: Path, env: Map[String, String]): IO[FrFlowApi] =
    IO.blocking(kb.problems ++ Generate.problems(kb)).flatMap { problems =>
      if problems.nonEmpty then IO.raiseError(FrFlowError.ModelProblems(problems)) else IO(new LiveApi(kb, ws, keyFile, env))
    }

  /** The developer's signing key: `FRFLOW_KEY`, or `~/.config/frflow/signing.key`, outside every repository. */
  def keyFile(env: Map[String, String], home: String): Path =
    env.get("FRFLOW_KEY").map(Path.of(_)).getOrElse(Path.of(home, ".config", "frflow", "signing.key"))
