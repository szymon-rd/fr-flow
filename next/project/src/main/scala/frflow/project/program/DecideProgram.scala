package frflow.project.program

import cats.effect.Clock
import cats.Monad
import cats.syntax.all.*
import frflow.decision.ledger.{Authorship, Counted, Deciders, Ledger, Seals}
import frflow.decision.review.{Reading, Subjects}
import frflow.decision.rules.{Command, Decide, Refusal}
import frflow.project.port.Records
import frflow.wire.file.Files
import frflow.wire.ledger.LedgerFile

/** `decide`: refused unless the key at hand is listed under the decider's name in the committed deciders' list, and
  * while the ledger no longer holds what was committed of some node (`Refusal.Rewritten`: restore it from the last
  * commit first), before any rule; then, under the ledger's lock, the rules on the ledger as it counts now
  * (`Counted`), and the decisions they add signed (their `after` set) and stored after every decision the ledger
  * keeps. `preview` says what a decision would record, storing and signing nothing.
  */
final class DecideProgram[F[_]: Monad: Clock](ports: Ports[F]):
  def apply(subjects: Subjects, c: Command, by: String): F[Either[Refusal, Decided]] =
    (authorship(by), counting, ports.keys.key, ports.ledger.load).tupled.flatMap { (author, count, key, now) =>
      if !count.deciders.exists(_.allows(by, key)) then Refusal.NotADecider(by).asLeft[Decided].pure[F]
      else count.refused(now).fold(ports.keys.signer.flatMap(sign => ports.ledger.update { before =>
        count.refused(before).toLeft(count(before).counting).flatMap { counted =>
          val r = Reading(subjects, counted)
          Decide(r, c, author).map { after =>
            val signed = Seals.signAdded(counted, after, sign)
            (Counted.stored(before, counted, signed), Decided(Decide.added(r, counted, signed)))
          }
        }
      }))(_.asLeft[Decided].pure[F])
    }

  def preview(subjects: Subjects, c: Command, by: String): F[Either[Refusal, Decided]] =
    (authorship(by), counting, ports.ledger.load).mapN { (author, count, l) =>
      val r = Reading(subjects, count(l).counting)
      Decide(r, c, author).map(after => Decided(Decide.added(r, r.ledger, after)))
    }

  private def authorship(by: String): F[Authorship] =
    (Clock[F].realTimeInstant, ports.git.head).mapN(Authorship(by, _, _))

  /** How a ledger counts: against the committed deciders' list, and every committed version of the ledger. */
  private def counting: F[DecideProgram.Counting] =
    (ports.keys.deciders, ports.keys.verifier, ports.git.versions(Records.path(LedgerFile.format)))
      .mapN((ds, verify, vs) => DecideProgram.Counting(ds, verify, vs.map(Files.read(LedgerFile.format, _).toOption)))

object DecideProgram:
  /** The deciders' list and the committed versions of the ledger a ledger counts against. */
  final case class Counting(deciders: Option[Deciders], verify: Seals.Verifier, committed: List[Option[Ledger]]):
    def apply(l: Ledger): Counted = Counted.of(l, deciders, verify, committed)
    /** Why nothing may be decided on `l`: what was committed of some node is not in it. */
    def refused(l: Ledger): Option[Refusal] =
      Option(apply(l).rewritten).filter(_.nonEmpty).map(Refusal.Rewritten(_))
