package frflow.api

import cats.effect.IO
import cats.syntax.all.*
import frflow.KnowledgeBase
import frflow.check.*
import frflow.lean.Generate
import frflow.ledger.{Decide, JsonStore, KeyStore, Refusal, Signing, Stamp}
import frflow.protocol.*
import java.nio.file.Path

/** The API over a project on disk. Each operation reads the workspace once (`Analysis.read`), computes, and
  * writes what it changed.
  */
final class LiveApi private (kb: KnowledgeBase, ws: Workspace, cfg: Config, lake: Lake, git: Git, ledger: JsonStore[Ledger],
    keys: KeyStore) extends FrFlowApi:
  private def analysis: IO[Analysis] = Analysis.read(kb, ws, cfg, ledger)
  private def viewOf(a: Analysis): IO[View] = IO.pure(View(a.annotated, a.warnings, a.unsigned.map(Logged.apply)))
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
      (trusted, filed) <- Keyring.read(ws)
      a <- analysis
      st <- (IO.realTimeInstant, git.head).parMapN(Stamp(_, _))
      // Another key under the name, or this key under another name: refused before anything is written.
      out <- trusted.refusal(by.name, key.public, filed).fold(ledger.update { before =>
        Decide(a.snapshot, before, d, by.name, st).map { after =>
          val signed = Signing.signNew(before, after, key)
          signed -> Decided.of(a.snapshot, before, signed)
        }
      })(r => IO.pure(Left(r)))
      _ <- out.traverse_(_ => keys.publish(key.public, by.name))
    yield out

  def developer(as: Option[String]): IO[Either[Refusal, Developer]] =
    as.map(_.trim).filter(_.nonEmpty).orElse(cfg.as).fold(keys.filedName)(n => IO.pure(Some(n)))
      .map(_.map(Developer.apply).toRight(Refusal.NoDeveloper))

  def render: IO[Rendered] = analysis.flatMap(a =>
    (CheckRunner.render(a), CheckRunner.writeSnapshot(a)).mapN((changed, file) => Rendered(changed, ws.root.relativize(file).toString)))

  /** Checks, and writes the snapshot with the results: the nodes checked, and the view after. */
  private def checked(node: Option[NodeId], progress: Progress => IO[Unit]): IO[(List[CheckedNode], View)] =
    for
      _ <- lake.available.ifM(IO.unit, IO.raiseError(FrFlowError.LeanMissing))
      _ <- node.traverse_(id => IO.fromOption(kb.node(id.value))(FrFlowError.UnknownNode(id)))
      a <- analysis
      (results, after) <- CheckRunner.check(a, lake, cfg, node.map(_.value), progress)
      _ <- CheckRunner.writeSnapshot(after)
      v <- viewOf(after)
      models = v.annotated.nodes.filter(r => node.forall(_ == r.id) && !results.exists(_._1.id == r.id.value))
    yield (results.flatMap((n, c) => v.node(NodeId(n.id)).map(CheckedNode.of(_, c))) ++ models.flatMap(CheckedNode.ofModel), v)

  def check(node: Option[NodeId], progress: Progress => IO[Unit]): IO[CheckReport] =
    checked(node, progress).map((ns, v) => CheckReport(ns, v, Overview.of(v)))
  def status: IO[StatusReport] = analysis.flatMap(a => CheckRunner.writeSnapshot(a) *> viewOf(a)).map(StatusReport.of)
  def ci(progress: Progress => IO[Unit]): IO[CiReport] =
    checked(None, progress).map((ns, v) => CiReport(ns.filter(_.status != CheckStatus.Proven), v, Trees.all(v)))

  override protected def relative(query: String): IO[String] =
    IO(Path.of(query).toAbsolutePath.normalize).map(p => if p.startsWith(ws.root) && p != ws.root then ws.root.relativize(p).toString else query)
      .handleError(_ => query)

  override protected def exists(path: String): IO[Boolean] =
    IO(java.nio.file.Files.exists(ws.root.resolve(path)) || java.nio.file.Files.exists(Path.of(path))).handleError(_ => false)

  def modelFingerprint: IO[Fingerprint] =
    Inputs.projectSources(ws.root, cfg.sources).flatMap(_.sorted.traverse(p => Disk.read(p).map(t => s"$p\u0000${t.getOrElse("")}")))
      .map(texts => Fingerprint(Sha(texts.mkString("\u0000"))))

  def scaffold(id: NodeId): IO[Scaffolded] =
    IO.fromOption(kb.node(id.value))(FrFlowError.UnknownNode(id)).flatMap(n =>
      analysis.flatMap(Scaffold(_, lake, n)).flatTap(_ => analysis.flatMap(CheckRunner.writeSnapshot)).map(Scaffolded(id, _)))

object LiveApi:
  /** The project in `ws`, run as `env` says (see `Config`); the model's problems, if any, fail it (nothing else is computed). */
  def apply(kb: KnowledgeBase, ws: Workspace, env: Map[String, String]): IO[FrFlowApi] =
    IO(kb.problems.map(_.message) ++ Generate.problems(kb)).flatMap(ps => IO.raiseWhen(ps.nonEmpty)(FrFlowError.ModelProblems(ps))) *>
      Config.load(env).flatMap { cfg =>
        (Lake(ws.lean, cfg), JsonStore.ledger(ws.ledgerFile))
          .mapN(new LiveApi(kb, ws, cfg, _, Git.at(ws.root), _, KeyStore.at(cfg.key, ws.keysDir)))
      }

  /** The project at `root` (`FRFLOW_ROOT` overrides it); `kernelPath` is FrFlow's Lean kernel relative to its `lean/`. */
  def fromEnv(kb: => KnowledgeBase, root: String, kernelPath: String, env: Map[String, String]): IO[FrFlowApi] =
    IO(Workspace(Path.of(env.getOrElse("FRFLOW_ROOT", root)).toAbsolutePath.normalize, kernelPath))
      .flatMap(ws => IO(kb).flatMap(frflow.check.WrittenExamples.load).flatMap(LiveApi(_, ws, env)))
