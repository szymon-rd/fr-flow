package frflow.api

import cats.effect.IO
import frflow.protocol.*
import scala.util.control.NoStackTrace

// The ledger's types a front end reads, so it imports only this package and the protocol's.
export frflow.ledger.{CodeProof, Decide, ForAgent, Found, Mention, Mentioned, Refusal}
export frflow.check.Progress

/** A project as its front ends open it: the knowledge base, its directory (`FRFLOW_ROOT` overrides it), and FrFlow's Lean
  * kernel relative to its `lean/`. A project's main object is one (the CLI's `FrFlowApp`); the web view's `serve` task
  * opens the same object.
  */
trait FrFlowProject:
  def kb: frflow.KnowledgeBase
  def root: String
  def kernelPath: String
  def api(env: Map[String, String]): IO[FrFlowApi] = LiveApi.fromEnv(kb, root, kernelPath, env)

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
  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[Refusal, Request]]
  /** An answer read, or a request withdrawn. */
  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]]
  /** Answers a request; given a node instead, tells the developer about work they did not ask for. */
  def answer(to: String, text: String): IO[Either[Refusal, RequestId]]
  // The conversation IDEA.md is written from, as the agent records it: a record, not decisions (the developer decides IDEA.md).
  /** What the developer said in chat, word for word. */
  def said(text: String): IO[Either[Refusal, Said]]
  /** A question the agent asked, with the answer it assumed: numbered Q1, Q2, … */
  def asked(text: String, assumed: String): IO[Either[Refusal, Question]]
  /** The developer's reply to a question, as they said it in chat; a later reply stands. */
  def replied(question: String, text: String): IO[Either[Refusal, Question]]
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
  def inbox: IO[Inbox] = reviewing.map(_._2)
  /** The inbox with the view it was read from: what a review walks, reading each node of that view. */
  def reviewing: IO[(View, Inbox)] = view.map(v => v -> Inbox.of(v))
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
