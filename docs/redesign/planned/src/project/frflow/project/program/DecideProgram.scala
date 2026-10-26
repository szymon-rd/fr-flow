package frflow.project.program

import cats.effect.Clock
import cats.Monad
import cats.syntax.all.*
import frflow.decision.ledger.{Authorship, Seals}
import frflow.decision.review.{Reading, Subjects}
import frflow.decision.rules.{Command, Decide, Refusal}
import frflow.project.port.{Git, KeyRing, LedgerStore}

/** `decide`: refused unless the key at hand is listed under the decider's name in the committed deciders' list; the
  * rules on the ledger as read, so a refusal touches no key; then, under the ledger's lock, the rules again on the
  * ledger as it is, and the added decisions signed (their `after` set) and stored.
  */
final class DecideProgram[F[_]: Monad: Clock](ledger: LedgerStore[F], keys: KeyRing[F], git: Git[F]):
  def apply(subjects: Subjects, c: Command, by: String): F[Either[Refusal, Decided]] =
    for
      author <- (Clock[F].realTimeInstant, git.head).mapN(Authorship(by, _, _))
      listed <- (keys.deciders, keys.key).mapN((ds, k) => ds.exists(_.allows(by, k)))
      first  <- ledger.load.map(l => Decide(Reading(subjects, l), c, author))
      out    <- first.filterOrElse(_ => listed, Refusal.NotADecider(by))
                  .fold(e => Monad[F].pure(Left(e)), _ => recorded(subjects, c, author))
    yield out

  private def recorded(subjects: Subjects, c: Command, author: Authorship): F[Either[Refusal, Decided]] =
    keys.signer.flatMap(sign => ledger.update { before =>
      val r = Reading(subjects, before)
      Decide(r, c, author).map { after =>
        val signed = Seals.signAdded(before, after, sign)
        (signed, Decided(Decide.added(r, before, signed)))
      }
    })
