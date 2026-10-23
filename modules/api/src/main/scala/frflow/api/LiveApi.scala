package frflow.api

import cats.effect.IO
import cats.syntax.all.*
import frflow.{KnowledgeBase, Node}
import frflow.check.*
import frflow.lean.{Generate, ObligationName}
import frflow.ledger.{KeyStore, Refusal, Signing, Stamp}
import frflow.protocol.*

/** The API over a project on disk: the check module's `Workflow` (the analysis, render, check, status,
  * context, scaffold, and the ledger's stores it holds) and the developer's key (`KeyStore`, `Signing`).
  * Thin on purpose: what it computes is in this package's pure objects and in the modules below.
  */
final class LiveApi private (kb: KnowledgeBase, workflow: Workflow, keys: KeyStore, env: Map[String, String]) extends FrFlowApi:
  private val ws = workflow.ws
  private val stores = workflow.stores

  def view: IO[View] = workflow.analysis.flatMap(viewOf(_))

  private def viewOf(a: Analysis, status: Option[Status] = None): IO[View] =
    stores.requests.load.map(View(status.getOrElse(Status.of(a)), _, unsigned(a.ledger, a)))

  private def unsigned(l: Ledger, a: Analysis): List[Unsigned] =
    Signing.unsigned(l, a.inputs.keys).map((id, d) => Unsigned(id, Ledger.entry(d), d))

  def codeChange(r: Reviewed): IO[Option[CodeChange]] = r.node.code.flatTraverse { c =>
    if r.state == ReviewState.Proposed then
      c.files.traverseFilter(f => Disk.read(ws.root.resolve(f)).map(_.map(text => s"--- $f (in full)\n$text")))
        .map(texts => Some(CodeChange(c.files, texts.mkString("\n"), inFull = true)))
    else Option.when(r.review.causes.contains(Cause.Code))(Details.binding(r)).flatten
      .traverse(d => workflow.codeSince(d, c.files).map(CodeChange(c.files, _, inFull = false)))
  }

  def history: IO[List[Logged]] = stores.ledger.load.map(_.all.map(Logged.apply))

  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    (workflow.analysis.flatMap(a => viewOf(a).tupleRight(a.ledger)), IO.realTimeInstant).mapN { case ((v, before), now) =>
      Deciding(v, before, d, by, Stamp(now.toString)).map(Deciding.added(v, before, _))
    }

  /** Records the decision on the ledger as it is on disk, signed with the developer's key; the key's
    * public half is filed under their name once the decision is recorded.
    */
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    for
      key <- keys.developer
      requests <- stores.requests.load
      out <- workflow.record { (a, stamp) => before =>
        val v = View(Status.of(a), requests, unsigned(before, a))
        Deciding(v, before, d, by, stamp).map { after =>
          val signed = Signing.signNew(before, after, key)
          signed -> Deciding.added(v, before, signed)
        }
      }
      _ <- out.traverse_(_ => keys.publish(key.public, by.name))
    yield out

  def sign(entries: Option[Set[EntryRef]], by: Developer): IO[Either[Refusal, List[Unsigned]]] =
    for
      key <- keys.developer
      a <- workflow.analysis
      out <- stores.ledger.update { l =>
        val all = unsigned(l, a)
        val chosen = entries.fold(all)(es => all.filter(u => es(u.entry)))
        val missing = entries.fold(List.empty[EntryRef])(es => (es -- all.map(_.entry)).toList)
        if missing.nonEmpty then Left(Refusal.NotUnsigned(missing))
        else if chosen.isEmpty then Left(Refusal.NothingToSign)
        else Right(Signing.signEntries(l, chosen.map(_.entry).toSet, key) -> chosen)
      }
      _ <- out.traverse_(_ => keys.publish(key.public, by.name))
    yield out

  def developer(as: Option[String]): IO[Either[Refusal, Developer]] =
    as.orElse(env.get("FRFLOW_AS")).map(_.trim).filter(_.nonEmpty).fold(keys.filedName)(n => IO.pure(Some(n)))
      .map(_.map(Developer.apply).toRight(Refusal.NoDeveloper))

  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[Refusal, Request]] =
    if text.trim.isEmpty then IO.pure(Left(Refusal.NoText))
    else node.filter(id => kb.node(id.value).isEmpty) match
      case Some(id) => IO.pure(Left(Refusal.UnknownNode(id)))
      case None =>
        node.flatTraverse(id => view.map(_.node(id).map(_.review.version)))
          .flatMap(seen => stores.requests.ask(node, text.trim, by.name, seen)).map(Right(_))

  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]] = stores.requests.close(ids)

  def answer(to: String, text: String): IO[Either[Refusal, RequestId]] =
    stores.requests.answer(to, text, id => kb.node(id.value).isDefined).map(_.map(_.id))

  def render: IO[Rendered] =
    for
      a <- workflow.analysis
      changed <- workflow.render(a)
      file <- workflow.writeSnapshot(a)
    yield Rendered(changed, ws.root.relativize(file).toString)

  def check(node: Option[NodeId]): IO[CheckReport] =
    for
      _ <- lean *> node.traverse_(this.node)
      c <- workflow.check(node.map(_.value))
      _ <- workflow.writeSnapshot(c.after)
      v <- viewOf(c.after)
    yield CheckReport(c.results.map(checked), v)

  def status: IO[View] = workflow.analysis.flatMap(a => workflow.writeSnapshot(a) *> viewOf(a))

  def ci: IO[CiReport] =
    lean *> workflow.ci.flatMap(c => viewOf(c.checked.after, Some(c.status))
      .map(CiReport(c.checked.results.filter(_._2.status != CheckStatus.Proven).map(checked), _)))

  def context(id: NodeId): IO[Context] = node(id).flatMap(workflow.context)

  def scaffold(id: NodeId): IO[Scaffolded] =
    node(id).flatMap(n => workflow.scaffold(n).flatTap(_ => workflow.writeSnapshot).map(Scaffolded(id, _)))

  private def node(id: NodeId): IO[Node[?]] = IO.fromOption(kb.node(id.value))(FrFlowError.UnknownNode(id.value))

  private def lean: IO[Unit] = workflow.lake.available.ifM(IO.unit, IO.raiseError(FrFlowError.LeanMissing))

  /** One node as `check` left it (see `CheckedNode`). */
  private def checked(n: Node[?], c: NodeCheck): CheckedNode =
    val failing = kb.exampleResults(n).filter(r => r.contract != "ok" || r.implementation.exists(_ != "ok"))
      .map(r => FailingExample(r.example.describe, r.verdict))
    val idle = ObligationName.Tried(TryKind.Idle).lean
    CheckedNode(NodeId(n.id), c.status,
      notProven = c.obligations.filter(r => !r.isEvaluation && !r.fine).map(_.name),
      problems = c.obligations.filterNot(_.fine),
      failing = failing,
      idle = c.obligations.find(r => r.name == idle && r.status == ObligationStatus.Idle).map(_.detail),
      // With an example failing the node may be false: no hint to prove it.
      messages = c.messages.filterNot(m => failing.nonEmpty && m.startsWith("prove it in")))

object LiveApi:
  /** The API over the project at `ws`, deciding with the key at `keyFile` (see `KeyStore.keyFile`); the
    * model's problems, if any, fail it (nothing else is computed).
    */
  def apply(kb: KnowledgeBase, ws: Workspace, keyFile: java.nio.file.Path, env: Map[String, String]): IO[FrFlowApi] =
    IO(kb.problems.map(_.message) ++ Generate.problems(kb)).flatMap { problems =>
      if problems.nonEmpty then IO.raiseError(FrFlowError.ModelProblems(problems))
      else Workflow(kb, ws).map(new LiveApi(kb, _, KeyStore.at(keyFile, ws.keysDir), env))
    }
