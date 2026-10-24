package frflow.api

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import frflow.ledger.{Decide, Refusal, Stamp}
import frflow.protocol.*
import java.time.Instant

/** The API over a fixed snapshot and its ledger in memory: the CLI's tests run on it. Decisions go through the ledger's
  * `Decide`, as the live API's do; nothing is signed.
  */
final class FakeApi(snapshot: Snapshot, ledger: Ref[IO, Ledger], model: Ref[IO, Fingerprint]) extends FrFlowApi:
  private val at = Stamp(Instant.parse("2026-01-04T12:00:00Z"))

  def view: IO[View] = ledger.get.map(Sample.view(snapshot, _))
  protected def codeChange(node: Reviewed): IO[Option[CodeChange]] =
    IO.pure(node.node.code.filter(_ => node.state == ReviewState.Proposed).map(c => CodeChange(c.files, "object Store", inFull = true)))
  def ledgerNow: IO[Ledger] = ledger.get
  // The project's files: those under src/.
  override protected def exists(path: String): IO[Boolean] = IO.pure(path.startsWith("src/"))

  private def decided(l: Ledger, d: Decide, by: Developer) =
    Decide(snapshot, l, d, by.name, at).map(after => after -> Decided.of(snapshot, l, after))
  def preview(d: Decide, by: Developer): IO[Either[Refusal, Decided]] = ledger.get.map(decided(_, d, by).map(_._2))
  def decide(d: Decide, by: Developer): IO[Either[Refusal, Decided]] =
    ledger.get.flatMap(l => decided(l, d, by).traverse((after, done) => ledger.set(after).as(done)))
  def developer(as: Option[String]): IO[Either[Refusal, Developer]] = IO.pure(Right(Developer(as.getOrElse(Sample.by))))

  private def unavailable[A]: IO[A] = IO.raiseError(new UnsupportedOperationException("not in the fake: it needs Lean"))
  def render: IO[Rendered] = unavailable
  def check(node: Option[NodeId], progress: Progress => IO[Unit]): IO[CheckReport] = unavailable
  def status: IO[StatusReport] = view.map(StatusReport.of)
  def ci(progress: Progress => IO[Unit]): IO[CiReport] = unavailable
  def scaffold(node: NodeId): IO[Scaffolded] = unavailable
  def modelFingerprint: IO[Fingerprint] = model.get
  /** As if someone edited the model's sources. */
  def editModel: IO[Unit] = model.update(f => Fingerprint(f.value + "'"))

object FakeApi:
  def apply(snapshot: Snapshot = Sample.snapshot, ledger: Ledger = Sample.ledgerNow): IO[FakeApi] =
    (Ref.of[IO, Ledger](ledger), Ref.of[IO, Fingerprint](Fingerprint("model"))).mapN(new FakeApi(snapshot, _, _))
