package frflow.project.check

import cats.data.NonEmptyList
import cats.effect.Clock
import cats.Monad
import cats.syntax.all.*
import frflow.project.pipeline.Analysis
import frflow.project.port.Lake
import frflow.proof.layout.Layout
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, Obligation}
import frflow.proof.reading.{Elaboration, ProofRules}
import frflow.proof.verdict.{Judge, ObligationStatus, ProverRun, Result, WholeCheck}

/** The theory's own check: `Whole.lean` built and each consistency and vacuity obligation judged (proven when its
  * witnesses or FrFlow's automation meet it, or the developer's proof file `Proofs/<Model>/Whole.lean` proves it,
  * owner §39; one nothing meets stays open, "consistency not proven" or "not shown"), then each example tried
  * against the claims beside it (shown or not); a module Lake did not run judges nothing; a proof is proven only with
  * its audit, on the axioms allowed; a proof file holding what it may not is failed. None when nothing is asked.
  */
final class WholeChecker[F[_]: Monad: Clock](lake: Lake[F]):
  def apply(a: Analysis): F[Option[WholeCheck]] =
    val layout = Layout(a.decided.theory.name)
    a.whole.toNel.traverse { asked =>
      (built(a, layout.whole), built(a, layout.wholeChecks), authored(a, layout), Clock[F].realTimeInstant)
        .mapN((whole, checks, proofs, at) =>
          WholeCheck(a.keys.whole, asked.toList.map(o => judged(o, whole, checks, proofs)), at))
    }

  private type Ran = Option[(ProverRun, Option[Elaboration])]

  /** A module's run, with what Lean said of it; none when the model has no such module. */
  private def built(a: Analysis, name: ModuleName): F[Ran] =
    a.modules.find(_.name == name).traverse(m => lake.build(NonEmptyList.one(name)).map(r => r -> Option.when(
      NodeLean.ran(name, r))(Elaboration(Print.module(m), NodeLean.output(r), m.name.file.value.stripPrefix("lean/")))))

  /** The developer's proof file, as Lean read it when building the audit of its proofs (which imports it), and the
    * audit; none when nothing asked is authored.
    */
  private def authored(a: Analysis, layout: Layout): F[Option[Authored]] =
    a.wholeProof.filter(_ => a.whole.exists(_.discharge == Discharge.Authored)).flatTraverse { f =>
      built(a, layout.wholeAudit).map(_.map((r, audit) => Authored(ProofRules.notAllowed(f).isEmpty,
        Option.when(NodeLean.ran(layout.wholeProofs, r))(Elaboration(f.source, NodeLean.output(r),
          layout.wholeProofs.file.value.stripPrefix("lean/"))), audit)))
    }

  private def judged(o: Obligation, whole: Ran, checks: Ran, proofs: Option[Authored]): Result =
    o.discharge match
      case Discharge.Attempt(_) => ran(o, checks)(Judge.tried(o.name, _))
      case Discharge.Authored   => proofs.fold(Result(o.name, ObligationStatus.Unchecked, Nil))(p =>
          if !p.allowed then Result(o.name, ObligationStatus.Failed, Nil)
          else p.proof.fold(Result(o.name, ObligationStatus.Unchecked, Nil))(e =>
            audited(o, Judge.required(o.name, e), p.audit)))
      case _                    => ran(o, whole)(e => audited(o, Judge.whole(o, e), Some(e)))

  private def ran(o: Obligation, in: Ran)(judge: Elaboration => Result): Result = in match
    case None                            => Result(o.name, ObligationStatus.Unchecked, Nil)
    case Some((ProverRun.TimedOut(_), _)) => Result(o.name, ObligationStatus.Timeout, Nil)
    case Some((_, None))                 => Result(o.name, o.discharge match
        case Discharge.Attempt(_) => ObligationStatus.NotShown
        case _                    => ObligationStatus.Unchecked, Nil)
    case Some((_, Some(e)))              => judge(e)

  /** Proven only with its audit, every axiom it rests on allowed; without one, not checked (fail closed). */
  private def audited(o: Obligation, r: Result, audit: Option[Elaboration]): Result =
    if r.status != ObligationStatus.Proven then r
    else audit.flatMap(_.axiomsOf(LowerObligation.name(o.name).text))
      .fold(r.copy(status = ObligationStatus.Unchecked))(as =>
        if as.forall(ProofRules.AllowedAxioms) then r else r.copy(status = ObligationStatus.Failed))
