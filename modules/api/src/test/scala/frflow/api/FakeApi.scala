package frflow.api

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import frflow.check.Context
import frflow.ledger.{Refusal, Stamp}
import frflow.protocol.*

/** The API over a fixed snapshot, its ledger and requests in memory: the CLI's tests run on it. Decisions
  * go through `Deciding`, as the live API's do; nothing is signed.
  */
final class FakeApi(snapshot: Snapshot, ledger: Ref[IO, Ledger], requests: Ref[IO, List[Request]]) extends FrFlowApi:
  private def at = Stamp("2026-01-04T12:00:00Z")

  def view: IO[View] = (ledger.get, requests.get).flatMapN((l, rs) => IO.pure(Sample.view(snapshot, l, rs)))
  def codeChange(node: Reviewed): IO[Option[CodeChange]] =
    IO.pure(node.node.code.filter(_ => node.state == ReviewState.Proposed).map(c => CodeChange(c.files, "object Store", inFull = true)))
  def history: IO[List[Logged]] = ledger.get.map(_.all.map(Logged.apply))
  def ledgerNow: IO[Ledger] = ledger.get

  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    (view, ledger.get).flatMapN((v, l) => IO.pure(Deciding(v, l, d, by, at).map(Deciding.added(v, l, _))))
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    (view, ledger.get).flatMapN { (v, l) =>
      Deciding(v, l, d, by, at).fold(e => IO.pure(Left(e)), after => ledger.set(after).as(Right(Deciding.added(v, l, after))))
    }
  def sign(entries: Option[Set[EntryRef]], by: Developer): IO[Either[Refusal, List[Unsigned]]] = IO.pure(Left(Refusal.NothingToSign))
  def developer(as: Option[String]): IO[Either[Refusal, Developer]] = IO.pure(Right(Developer(as.getOrElse(Sample.by))))

  def ask(node: Option[NodeId], text: String, by: Developer): IO[Either[Refusal, Request]] =
    view.flatMap { v =>
      requests.modify { rs =>
        val r = Request(RequestId(s"R${rs.size + 1}"), node, text, by.name, at.at.take(19) + "Z", RequestStatus.Open,
          seen = node.flatMap(v.node).map(_.review.version))
        (rs :+ r, Right(r))
      }
    }
  def close(ids: List[RequestId]): IO[Either[Refusal, List[Request]]] =
    requests.modify(rs => (rs.map(r => if ids.contains(r.id) then r.copy(status = RequestStatus.Closed) else r), Right(rs.filter(r => ids.contains(r.id)))))
  def answer(to: String, text: String): IO[Either[Refusal, RequestId]] =
    requests.modify { rs =>
      rs.find(_.id == RequestId(to)).fold((rs, Left(Refusal.UnknownRequest(to)))) { r =>
        (rs.map(x => if x.id == r.id then x.copy(status = RequestStatus.Answered, answer = Some(text)) else x), Right(r.id))
      }
    }

  private def unavailable[A]: IO[A] = IO.raiseError(new UnsupportedOperationException("not in the fake: it needs Lean"))
  def render: IO[Rendered] = unavailable
  def check(node: Option[NodeId]): IO[CheckReport] = unavailable
  def status: IO[View] = view
  def ci: IO[CiReport] = unavailable
  def context(node: NodeId): IO[Context] = unavailable
  def scaffold(node: NodeId): IO[Scaffolded] = unavailable

object FakeApi:
  def apply(snapshot: Snapshot = Sample.snapshot, ledger: Ledger = Sample.ledgerNow, requests: List[Request] = Sample.requests): IO[FakeApi] =
    (Ref.of[IO, Ledger](ledger), Ref.of[IO, List[Request]](requests)).mapN(new FakeApi(snapshot, _, _))
