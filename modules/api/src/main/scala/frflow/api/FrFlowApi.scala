package frflow.api

import cats.effect.IO
import frflow.protocol.*
import java.nio.file.Path
import scala.util.control.NoStackTrace

// The ledger's types a front end reads, so it imports only this package and the protocol's.
export frflow.ledger.{CodeProof, Decide, Found, Mention, Mentioned, Refusal}
export frflow.check.Progress

/** A layer on top of FrFlow, such as an AI agent's tools: a project's main object lists the ones it uses, and each front
  * end takes the parts it knows (the CLI's `CliExtension`, the web view's `WebExtension`). FrFlow itself needs none.
  */
trait Extension

/** What a layer on top works with: the project's API, its directory (where it keeps its own files, under `.frflow/`),
  * and the environment.
  */
final case class Host(api: FrFlowApi, directory: Path, env: Map[String, String])

/** A project as its front ends open it: the knowledge base, its directory (`FRFLOW_ROOT` overrides it), FrFlow's Lean
  * kernel relative to its `lean/`, and the layers on top it uses. A project's main object is one (the CLI's `FrFlowApp`);
  * the web view's `serve` task opens the same object.
  */
trait FrFlowProject:
  def kb: frflow.KnowledgeBase
  def root: String
  def kernelPath: String
  def extensions: List[Extension] = Nil
  def directory(env: Map[String, String]): Path = Path.of(env.getOrElse("FRFLOW_ROOT", root)).toAbsolutePath.normalize
  def api(env: Map[String, String]): IO[FrFlowApi] = LiveApi.fromEnv(kb, root, kernelPath, env)
  def host(env: Map[String, String]): IO[Host] = api(env).map(Host(_, directory(env), env))

/** What fails a command (refusals a user reads are `Refusal`s instead): mapped once, at each front end. */
enum FrFlowError(val message: String) extends Exception(message) with NoStackTrace:
  /** The model does not hold together: nothing else is computed until it does. */
  case ModelProblems(problems: List[String]) extends FrFlowError(problems.mkString("\n"))
  case UnknownNode(id: NodeId) extends FrFlowError(s"unknown node $id")
  case LeanMissing extends FrFlowError("lake not found (set FRFLOW_LAKE)")

/** FrFlow as a front end sees it: typed values, never text. The primitives read and write the project; the
  * rest is computed here from the `view`.
  */
trait FrFlowApi:
  def view: IO[View]
  protected def codeChange(node: Reviewed): IO[Option[CodeChange]]
  /** The decisions `d` would record, without recording them. */
  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]]
  /** Records `d`, signed with the developer's key (its public key filed in `.frflow/keys` on first use). */
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]]
  /** Who decides: `as`, else `FRFLOW_AS`, else the name the developer's key is filed under. */
  def developer(as: Option[String]): IO[Either[Refusal, Developer]]
  def render: IO[Rendered]
  /** `progress` hears of each level of the check before Lean proves it. */
  def check(node: Option[NodeId], progress: Progress => IO[Unit] = _ => IO.unit): IO[CheckReport]
  /** The view, with the snapshot written. */
  def status: IO[StatusReport]
  def ci(progress: Progress => IO[Unit] = _ => IO.unit): IO[CiReport]
  def scaffold(node: NodeId): IO[Scaffolded]
  /** The model's sources as they are on disk now. A process that keeps running (`serve`) compiled its model when it
    * started: once this moves, what it shows mixes that model with the files of another, and is not decided on.
    */
  def modelFingerprint: IO[Fingerprint]
  /** A path as the project names it: relative to its directory (a path from elsewhere is given as it is). */
  protected def relative(query: String): IO[String] = IO.pure(query)

  def tree(from: Option[NodeId]): IO[Tree] =
    view.flatMap(v => from.fold(IO.pure(Trees.all(v)))(id => IO.fromOption(Trees.from(v, id))(FrFlowError.UnknownNode(id))))
  /** `aside`: the nodes a layer on top holds back from the developer's queue (see `Inbox.of`). */
  def inbox(aside: View => IO[Set[NodeId]] = FrFlowApi.noneAside): IO[Inbox] = reviewing(aside).map(_._2)
  /** The inbox with the view it was read from: what a review walks, reading each node of that view. */
  def reviewing(aside: View => IO[Set[NodeId]] = FrFlowApi.noneAside): IO[(View, Inbox)] =
    view.flatMap(v => aside(v).map(held => v -> Inbox.of(v, held)))
  /** Whether a path the project names is a file or a directory. */
  protected def exists(path: String): IO[Boolean] = IO.pure(true)
  def find(v: View, query: String): IO[Found] = relative(query).flatMap(q => frflow.ledger.Find(v.annotated, q) match
    case Found.Ungoverned(path) => exists(path).map(if _ then Found.Ungoverned(path) else Found.Missing(path))
    case found => IO.pure(found))
  def details(id: NodeId): IO[NodeDetails] = withNode(id)(details)
  def details(v: View, r: Reviewed): IO[NodeDetails] = codeChange(r).map(Details.of(v, r, _))
  def diff(id: NodeId): IO[NodeDiff] = withNode(id)(diff)
  def diff(v: View, r: Reviewed): IO[NodeDiff] = codeChange(r).map(Details.diff(v, r, _))

  protected def withNode[A](id: NodeId)(f: (View, Reviewed) => IO[A]): IO[A] =
    view.flatMap(v => v.node(id).fold(IO.raiseError(FrFlowError.UnknownNode(id)))(f(v, _)))

object FrFlowApi:
  val noneAside: View => IO[Set[NodeId]] = _ => IO.pure(Set.empty)
