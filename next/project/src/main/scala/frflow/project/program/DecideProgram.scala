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

/** `decide`: refused unless the key at hand is listed under the decider's name in the committed deciders' list,
  * before any rule; then, under the ledger's lock, the rules on the ledger as it counts now (`Counted`), and the
  * decisions they add signed (their `after` set) and stored after every decision the ledger keeps. `preview` says
  * what a decision would record, storing and signing nothing.
  */
final class DecideProgram[F[_]: Monad: Clock](ports: Ports[F]):
  def apply(subjects: Subjects, c: Command, by: String): F[Either[Refusal, Decided]] =
    (authorship(by), counting, ports.keys.key).tupled.flatMap { (author, count, key) =>
      if !count.deciders.exists(_.allows(by, key)) then Refusal.NotADecider(by).asLeft[Decided].pure[F]
      else ports.keys.signer.flatMap(sign => ports.ledger.update { before =>
        val counted = count(before)
        val r = Reading(subjects, counted)
        Decide(r, c, author).map { after =>
          val signed = Seals.signAdded(counted, after, sign)
          (Counted.stored(before, counted, signed), Decided(Decide.added(r, counted, signed)))
        }
      })
    }

  def preview(subjects: Subjects, c: Command, by: String): F[Either[Refusal, Decided]] =
    (authorship(by), counting, ports.ledger.load).mapN { (author, count, l) =>
      val r = Reading(subjects, count(l))
      Decide(r, c, author).map(after => Decided(Decide.added(r, r.ledger, after)))
    }

  private def authorship(by: String): F[Authorship] =
    (Clock[F].realTimeInstant, ports.git.head).mapN(Authorship(by, _, _))

  /** How a ledger counts: against the committed deciders' list, and the ledger as committed. */
  private def counting: F[DecideProgram.Counting] =
    (ports.keys.deciders, ports.keys.verifier, ports.git.committed(Records.path(LedgerFile.format)))
      .mapN((ds, verify, at) => DecideProgram.Counting(ds, verify, at.flatMap(Files.read(LedgerFile.format, _)
        .toOption)))

object DecideProgram:
  /** The deciders' list and the committed ledger a ledger counts against. */
  final case class Counting(deciders: Option[Deciders], verify: Seals.Verifier, committed: Option[Ledger]):
    def apply(l: Ledger): Ledger = Counted.of(l, deciders, verify, committed).counting
