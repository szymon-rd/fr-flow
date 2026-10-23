package frflow.api

import cats.effect.IO
import cats.syntax.all.*
import frflow.KnowledgeBase
import frflow.check.*
import frflow.lean.Generate
import frflow.ledger.{Decide, JsonStore, KeyStore, Refusal, Requests, Signing, Stamp}
import frflow.protocol.*
import java.nio.file.Path

/** The API over a project on disk. Each operation reads the workspace once (`Analysis.read`), computes, and
  * writes what it changed.
  */
final class LiveApi private (kb: KnowledgeBase, ws: Workspace, cfg: Config, lake: Lake, git: Git, ledger: JsonStore[Ledger],
    requests: JsonStore[List[Request]], keys: KeyStore, env: Map[String, String]) extends FrFlowApi:
  private def analysis: IO[Analysis] = Analysis.read(kb, ws, cfg, ledger)
  private def viewOf(a: Analysis): IO[View] = requests.load.map(View(a.annotated, a.warnings, _, a.unsigned.map(Logged.apply)))
  def view: IO[View] = analysis.flatMap(viewOf)

  protected def codeChange(r: Reviewed): IO[Option[CodeChange]] = r.node.code.flatTraverse { c =>
    if r.state == ReviewState.Proposed then
      c.files.traverseFilter(f => Disk.read(ws.root.resolve(f)).map(_.map(text => s"--- $f (in full)\n$text")))
        .map(texts => Some(CodeChange(c.files, texts.mkString("\n"), inFull = true)))
    else r.review.binding.filter(_ => r.review.causes.contains(Cause.Code))
      .traverse(d => git.diff(d.commit.getOrElse(""), c.files).map(CodeChange(c.files, _, inFull = false)))
  }

  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    (analysis, IO.realTimeInstant).parMapN((a, now) => Decide(a.snapshot, a.ledger, d, by.name, Stamp(now)).map(Decided.of(a.snapshot, a.ledger, _)))

  // Decided on the ledger as it is on disk; the key's public half is filed once the decision is recorded.
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    for
      key <- keys.developer
      a <- analysis
      st <- (IO.realTimeInstant, git.head).parMapN(Stamp(_, _))
      out <- ledger.update { before =>
        Decide(a.snapshot, before, d, by.name, st).map { after =>
          val signed = Signing.signNew(before, after, key)
          signed -> Decided.of(a.snapshot, before, signed)
        }
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
        (node.flatTraverse(id => view.map(_.node(id).map(_.review.version))), IO.realTimeInstant).flatMapN((seen, now) =>
          requests.update[Refusal, Request](rs => Right(Requests.ask(rs, node, text.trim, by.name, now, seen))))

  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]] = requests.update(Requests.close(_, ids))
  def answer(to: String, text: String): IO[Either[Refusal, RequestId]] =
    IO.realTimeInstant.flatMap(now => requests.update(Requests.answer(_, to, text, id => kb.node(id.value).isDefined, now))).map(_.map(_.id))

  def render: IO[Rendered] = analysis.flatMap(a =>
    (CheckRunner.render(a), CheckRunner.writeSnapshot(a)).mapN((changed, file) => Rendered(changed, ws.root.relativize(file).toString)))

  /** Checks, and writes the snapshot with the results: the nodes checked, and the view after. */
  private def checked(node: Option[NodeId], progress: Progress => IO[Unit]): IO[(List[CheckedNode], View)] =
    for
      _ <- lake.available.ifM(IO.unit, IO.raiseError(FrFlowError.LeanMissing))
      _ <- node.traverse_(id => IO.fromOption(kb.node(id.value))(FrFlowError.UnknownNode(id.value)))
      a <- analysis
      (results, after) <- CheckRunner.check(a, lake, cfg, node.map(_.value), progress)
      _ <- CheckRunner.writeSnapshot(after)
      v <- viewOf(after)
    yield (results.flatMap((n, c) => v.node(NodeId(n.id)).map(CheckedNode.of(_, c))), v)

  def check(node: Option[NodeId], progress: Progress => IO[Unit]): IO[CheckReport] = checked(node, progress).map(CheckReport.apply)
  def status: IO[View] = analysis.flatMap(a => CheckRunner.writeSnapshot(a) *> viewOf(a))
  def ci(progress: Progress => IO[Unit]): IO[CiReport] = checked(None, progress).map((ns, v) => CiReport(ns.filter(_.status != CheckStatus.Proven), v))

  override protected def relative(query: String): IO[String] =
    IO(Path.of(query).toAbsolutePath.normalize).map(p => if p.startsWith(ws.root) && p != ws.root then ws.root.relativize(p).toString else query)
      .handleError(_ => query)

  def scaffold(id: NodeId): IO[Scaffolded] =
    IO.fromOption(kb.node(id.value))(FrFlowError.UnknownNode(id.value)).flatMap(n =>
      analysis.flatMap(Scaffold(_, lake, n)).flatTap(_ => analysis.flatMap(CheckRunner.writeSnapshot)).map(Scaffolded(id, _)))

object LiveApi:
  /** Deciding with the key at `keyFile`; the model's problems, if any, fail it (nothing else is computed). */
  def apply(kb: KnowledgeBase, ws: Workspace, keyFile: Path, env: Map[String, String]): IO[FrFlowApi] =
    IO(kb.problems.map(_.message) ++ Generate.problems(kb)).flatMap(ps => IO.raiseWhen(ps.nonEmpty)(FrFlowError.ModelProblems(ps))) *>
      Config.load.flatMap(cfg => (Lake(ws.lean, cfg), JsonStore.make(ws.ledgerFile, Ledger.empty), JsonStore.make(ws.requestsFile, List.empty[Request]))
        .mapN(new LiveApi(kb, ws, cfg, _, Git.at(ws.root), _, _, KeyStore.at(keyFile, ws.keysDir), env)))

  /** The project at `root` (`FRFLOW_ROOT` overrides it), deciding with the key the environment names (`FRFLOW_KEY`,
    * or the one under the home directory); `kernelPath` is FrFlow's Lean kernel relative to its `lean/`.
    */
  def fromEnv(kb: => KnowledgeBase, root: String, kernelPath: String, env: Map[String, String]): IO[FrFlowApi] =
    IO(sys.props.getOrElse("user.home", ".")).flatMap { home =>
      val ws = Workspace(Path.of(env.getOrElse("FRFLOW_ROOT", root)).toAbsolutePath.normalize, kernelPath)
      IO(kb).flatMap(LiveApi(_, ws, KeyStore.keyFile(env, Path.of(home)), env))
    }
