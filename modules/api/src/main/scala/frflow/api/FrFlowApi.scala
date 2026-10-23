package frflow.api

import cats.effect.IO
import frflow.check.Context
import frflow.protocol.*
import scala.util.control.NoStackTrace

// The ledger's types a front end reads, so it imports only this package and the protocol's.
export frflow.ledger.{CodeProof, Decide, ForAgent, Found, Mention, Mentioned, Refusal}

/** Where a change belongs, in a view (see the ledger's `Find`). */
object Find:
  def apply(v: View, query: String): Found = frflow.ledger.Find(v.annotated, query)

/** What fails a command (refusals a user reads are `Refusal`s instead): mapped once, at each front end. */
enum FrFlowError(val message: String) extends Exception(message) with NoStackTrace:
  /** The model does not hold together: nothing else is computed until it does. */
  case ModelProblems(problems: List[String]) extends FrFlowError(problems.mkString("\n"))
  case UnknownNode(id: String) extends FrFlowError(s"unknown node $id")
  case LeanMissing extends FrFlowError("lake not found (set FRFLOW_LAKE)")

/** FrFlow as a front end sees it: the one place a CLI, or a web view, calls. Every operation returns
  * typed values (the protocol's, and this package's), never text; a refusal is a `Refusal`.
  *
  * The primitives read and write the project; the rest is computed from the `view`, here, once.
  */
trait FrFlowApi:
  /** The snapshot with the developer's decisions, the requests, what is not signed, the warnings. */
  def view: IO[View]
  /** How the code a node governs changed since it was decided; never decided, the files in full. */
  protected def codeChange(node: Reviewed): IO[Option[CodeChange]]

  /** The decisions `d` would record, without recording them. */
  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]]
  /** Records `d`, signed with the developer's key (its public key filed in `.frflow/keys` on first use). */
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]]
  /** Who decides: `as`, else `FRFLOW_AS`, else the name the developer's key is filed under. */
  def developer(as: Option[String]): IO[Either[Refusal, Developer]]

  /** Asks the agent for a change, on a node or on the idea (no node). */
  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[Refusal, Request]]
  /** Closes requests: an answer read, or a request withdrawn. */
  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]]
  /** The agent answers a request, or, given a node, tells the developer about work they did not ask for. */
  def answer(to: String, text: String): IO[Either[Refusal, RequestId]]

  def render: IO[Rendered]
  def check(node: Option[NodeId]): IO[CheckReport]
  /** The view, with the snapshot written (so it shows what `status` says). */
  def status: IO[View]
  def ci: IO[CiReport]
  def context(node: NodeId): IO[Context]
  def scaffold(node: NodeId): IO[Scaffolded]

  def tree(from: Option[NodeId]): IO[Tree] =
    view.flatMap(v => IO.fromEither(Trees.of(v, from, Overview.of(v)).left.map(_ => FrFlowError.UnknownNode(from.fold("")(_.value)))))
  def overview: IO[Overview] = view.map(Overview.of)
  def inbox: IO[Inbox] = view.map(Inbox.of)
  def find(query: String): IO[Found] = view.map(Find(_, query))

  def details(id: NodeId): IO[NodeDetails] = withNode(id)((v, r) => codeChange(r).map(Details.of(v, r, _)))
  def diff(id: NodeId): IO[NodeDiff] = withNode(id)((v, r) => codeChange(r).map(Details.diff(v, r, _)))

  protected def withNode[A](id: NodeId)(f: (View, Reviewed) => IO[A]): IO[A] =
    view.flatMap(v => v.node(id).fold(IO.raiseError(FrFlowError.UnknownNode(id.value)))(f(v, _)))
