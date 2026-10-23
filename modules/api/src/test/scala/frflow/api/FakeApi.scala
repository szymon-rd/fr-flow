package frflow.api

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import frflow.ledger.{Decide, Refusal, Requests, Stamp}
import frflow.protocol.*
import java.time.Instant

/** The API over a fixed snapshot, its ledger and requests in memory: the CLI's tests run on it. Decisions
  * and requests go through the ledger's `Decide` and `Requests`, as the live API's do; nothing is signed.
  */
final class FakeApi(snapshot: Snapshot, ledger: Ref[IO, Ledger], requests: Ref[IO, List[Request]]) extends FrFlowApi:
  private val at = Stamp(Instant.parse("2026-01-04T12:00:00Z"))

  def view: IO[View] = (ledger.get, requests.get).flatMapN((l, rs) => IO.pure(Sample.view(snapshot, l, rs)))
  protected def codeChange(node: Reviewed): IO[Option[CodeChange]] =
    IO.pure(node.node.code.filter(_ => node.state == ReviewState.Proposed).map(c => CodeChange(c.files, "object Store", inFull = true)))
  def ledgerNow: IO[Ledger] = ledger.get

  private def decided(l: Ledger, d: Decide, by: Developer) =
    Decide(snapshot, l, d, by.name, at).map(after => after -> Decided.of(snapshot, l, after))
  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]] = ledger.get.map(decided(_, d, by).map(_._2))
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    ledger.get.flatMap(l => decided(l, d, by).traverse((after, done) => ledger.set(after).as(done)))
  def developer(as: Option[String]): IO[Either[Refusal, Developer]] = IO.pure(Right(Developer(as.getOrElse(Sample.by))))

  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[Refusal, Request]] =
    view.flatMap(v => requests.modify(Requests.ask(_, node, text, by.name, at.at, node.flatMap(v.node).map(_.review.version))).map(Right(_)))
  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]] = change(Requests.close(_, ids))
  def answer(to: String, text: String): IO[Either[Refusal, RequestId]] =
    change(Requests.answer(_, to, text, id => snapshot.nodes.exists(_.id == id), at.at)).map(_.map(_.id))
  private def change[A](f: List[Request] => Either[Refusal, (List[Request], A)]): IO[Either[Refusal, A]] =
    requests.modify(rs => f(rs).fold(e => (rs, Left(e)), (next, a) => (next, Right(a))))

  private def unavailable[A]: IO[A] = IO.raiseError(new UnsupportedOperationException("not in the fake: it needs Lean"))
  def render: IO[Rendered] = unavailable
  def check(node: Option[NodeId], progress: Progress => IO[Unit]): IO[CheckReport] = unavailable
  def status: IO[View] = view
  def ci(progress: Progress => IO[Unit]): IO[CiReport] = unavailable
  def scaffold(node: NodeId): IO[Scaffolded] = unavailable

object FakeApi:
  def apply(snapshot: Snapshot = Sample.snapshot, ledger: Ledger = Sample.ledgerNow, requests: List[Request] = Sample.requests): IO[FakeApi] =
    (Ref.of[IO, Ledger](ledger), Ref.of[IO, List[Request]](requests)).mapN(new FakeApi(snapshot, _, _))
