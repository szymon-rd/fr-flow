package frflow.project.check

import cats.data.{EitherT, NonEmptyList}
import cats.effect.Clock
import cats.Monad
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.project.port.{ProjectFiles, Prover}
import frflow.proof.layout.NodePart
import frflow.proof.lean.ast.ModuleName
import frflow.proof.rocq.RocqProject
import frflow.proof.obligation.{Discharge, Obligation, ObligationName}
import frflow.proof.reading.{Elaboration, TheoremVerdict}
import frflow.proof.verdict.*

/** One node's check: Rocq's steps, each a build followed by a pure judge (`proof.verdict.Judge`) that may end the
  * check there. The model first (`Spec`); the proof file's rules and the shared lemmas; `complete` (by automation,
  * or the proof file), refuted on a case when it does not go through and its one part fixes an answer; `impl`; the
  * composition `holds`; then the checks module lemma by lemma (each obligation proven or not, each try shown or
  * not: a try Rocq does not prove shows nothing); and a root's `root_impl`. A module Rocq did not run (one it
  * imports did not go through) proves nothing and shows nothing; a proof whose audit (`Print Assumptions`) Rocq did
  * not print is not checked (fail closed). `Judge.node` ends a check that got through, on the axioms each proof that
  * went through rests on, `parts` the statuses of its parts.
  */
final class NodeChecker[F[_]: Monad: Clock](prover: Prover[F], files: ProjectFiles[F], refutations: Refutations[F]):
  private type Step[A] = EitherT[F, Judged, A]
  /** Outcomes, and the axioms the proven ones rest on. */
  private type Judging = (List[Result], List[String])
  private val none: Step[Judging] = EitherT.pure((Nil, Nil))

  def apply(a: Analysis, n: NodeId, parts: List[CheckStatus]): F[NodeCheck] =
    val lean = NodeRocq(a, n)
    val steps: Step[Judged] =
      for
        _             <- run(lean.module(NodePart.Spec)).flatMap(r => stop(Judge.model(r)))
        _             <- proofFile(lean)
        (done, found, rests) <- complete(lean, a)
        impl          <- proven(lean, ObligationName.Impl)
        holds         <- composed(lean, done, parts)
        checks        <- checked(lean)
        root          <- rootImpl(lean)
      yield
        val (results, axioms) =
          (done ++ impl._1 ++ checks._1 ++ root._1, rests ++ holds ++ impl._2 ++ checks._2 ++ root._2)
        val j = Judge.node(results, axioms, parts)
        // A step Rocq refutes on a case is false, not open.
        val refuted = found.exists { case Finding.StepRefuted(_) => true; case _ => false }
        j.copy(status = if refuted then CheckStatus.Failed else j.status, findings = j.findings ++ found)
    steps.merge.flatMap(j => Clock[F].realTimeInstant.map(NodeCheck(n, a.keys.node(n), j.status, j.results,
      j.findings, _)))

  private def stop(j: Option[Judged]): Step[Unit] = EitherT.fromEither(j.toLeft(()))

  /** A build: Rocq's report, or the check ended when it timed out. */
  private def run(m: ModuleName): Step[ProverRun] =
    EitherT(prover.build(NonEmptyList.one(m)).map {
      case ProverRun.TimedOut(_) => Left(Judged(CheckStatus.Timeout, Nil, List(Finding.TimedOut)))
      case done                  => Right(done)
    })

  /** The proof file: only what one may contain; the shared lemmas it imports, every one of them proven. */
  private def proofFile(lean: NodeRocq): Step[Unit] = lean.proof.fold(EitherT.pure[F, Judged](())) { f =>
    stop(Judge.proofFile(f)) >> lean.lemmas.fold(EitherT.pure[F, Judged](()))(l =>
      run(lean.layout.lemmas).flatMap(r => stop(Judge.lemmas(l, r))))
  }

  /** `complete`, proven only with its audit (the `Auto` module's `Print Assumptions`, which imports the developer's
    * proof when there is one), and when neither automation nor the developer's proof proves it, a case Rocq proves
    * refutes the step.
    */
  private def complete(lean: NodeRocq, a: Analysis): Step[(List[Result], List[Finding], List[String])] =
    lean.required(ObligationName.Complete).fold(EitherT.pure[F, Judged]((List.empty[Result], List.empty[Finding],
      List.empty[String]))) { o =>
        val authored = o.discharge == Discharge.Authored
        run(lean.module(NodePart.Auto)).flatMap { r =>
          val audit = lean.elaborated(NodePart.Auto, r)
          val (results, axioms) = auditedBy(o, if authored then lean.elaboratedProof(r) else audit, audit, "complete")
          if results.forall(_.status == ObligationStatus.Proven) then EitherT.pure((results, Nil, axioms))
          else EitherT.liftF(refuted(lean, a).map(f => (results, f.toList, axioms)))
        }
    }

  /** A case refuting the step, searched for now, which Rocq proves refutes it. */
  private def refuted(lean: NodeRocq, a: Analysis): F[Option[Finding]] =
    refutations.of(a, lean.node).flatMap(_.flatTraverse(found => lean.refutes(found).flatTraverse { (m, text) =>
      files.writeIfChanged(RocqProject.path(m.name), text) >> prover.build(NonEmptyList.one(m.name)).map(r =>
        Option.when(NodeRocq.said(m, text, r).exists(_.verdict("refutes") == TheoremVerdict.Proven))(
          Finding.StepRefuted(found.inputs)))
    }))

  /** `impl`, in a module of its own, with the axioms its proof rests on when it goes through. */
  private def proven(lean: NodeRocq, name: ObligationName): Step[Judging] =
    lean.required(name).filter(_ => lean.has(NodePart.Impl)).fold(none)(o =>
      run(lean.module(NodePart.Impl)).map(r => audited(lean, o, lean.elaborated(NodePart.Impl, r))))

  /** `holds`, composed once `complete` is proven, with the axioms it rests on: a composition Rocq does not accept
    * fails the check, but while a part is not proven yet (its theorem may be what does not build), the node waits.
    */
  private def composed(lean: NodeRocq, done: List[Result], parts: List[CheckStatus]): Step[List[String]] =
    if !lean.has(NodePart.Theorems) || !done.forall(_.status == ObligationStatus.Proven) then EitherT.pure(Nil)
    else run(lean.module(NodePart.Theorems)).flatMap { r =>
      val e = lean.elaborated(NodePart.Theorems, r)
      r match
        case ProverRun.Failed(_) if !parts.forall(_ == CheckStatus.Proven) =>
          EitherT.leftT(Judged(CheckStatus.Waiting, done, Nil))
        case ProverRun.Failed(_) => EitherT.leftT(Judged(CheckStatus.Failed, done,
          List(Finding.NotProven(e.toList.flatMap(_.diagnostics.filter(_.error))))))
        case _                   => e.flatMap(_.axiomsOf("holds")).fold(
          EitherT.leftT[F, List[String]](Judged(CheckStatus.Open, done, List(Finding.NotProven(Nil)))))(
          EitherT.pure(_))
    }

  /** The checks module, theorem by theorem: each other obligation, each try. */
  private def checked(lean: NodeRocq): Step[Judging] =
    if !lean.has(NodePart.Checks) then none
    else run(lean.module(NodePart.Checks)).map { r =>
      val e = lean.elaborated(NodePart.Checks, r)
      val others = lean.others.map(o => audited(lean, o, e))
      val tries = lean.tried.map(o => e.fold(Result(o.name, ObligationStatus.NotShown, Nil))(Judge.tried(o.name, _)))
      (others.flatMap(_._1) ++ tries, others.flatMap(_._2))
    }

  /** A root's `root_impl`: proven when Rocq proves it, with the axioms it rests on. */
  private def rootImpl(lean: NodeRocq): Step[Judging] =
    if !lean.rooted then none
    else run(lean.layout.rootImpl).map { r =>
      val e = lean.elaboratedRoot(r)
      val verdict = e.fold(TheoremVerdict.Missing)(_.verdict("root_impl"))
      val result = verdict match
        case TheoremVerdict.Proven     => Result(ObligationName.RootImpl, ObligationStatus.Proven, Nil)
        case TheoremVerdict.Failed(es) => Result(ObligationName.RootImpl, ObligationStatus.Open, es)
        case _                         => Result(ObligationName.RootImpl, ObligationStatus.Open, Nil)
      val audit = e.flatMap(_.axiomsOf("root_impl"))
      if verdict == TheoremVerdict.Proven && audit.isEmpty then (List(result.copy(status = ObligationStatus.Unchecked)),
        Nil)
      else (List(result), audit.toList.flatten)
    }

  /** An obligation judged where Rocq ran on it; not checked where it did not. */
  private def judged(o: Obligation, e: Option[Elaboration]): Result =
    e.fold(Result(o.name, ObligationStatus.Unchecked, Nil))(Judge.required(o.name, _))

  /** Proven only with the axioms its audit lists (fail closed): one Rocq says nothing of is not checked. */
  private def audited(lean: NodeRocq, o: Obligation, e: Option[Elaboration]): Judging =
    auditedBy(o, e, e, lean.named(o))

  /** Judged where it is proven (`e`), its axioms read where they are printed (`audit`). */
  private def auditedBy(o: Obligation, e: Option[Elaboration], audit: Option[Elaboration], name: String): Judging =
    val result = judged(o, e)
    if result.status != ObligationStatus.Proven then (List(result), Nil)
    else audit.flatMap(_.axiomsOf(name))
      .fold((List(result.copy(status = ObligationStatus.Unchecked)), Nil))(as => (List(result), as))
