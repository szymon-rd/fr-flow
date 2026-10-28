package frflow.project.check

import cats.data.{EitherT, NonEmptyList}
import cats.effect.Clock
import cats.Monad
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.project.port.{Lake, ProjectFiles}
import frflow.proof.layout.NodePart
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, Obligation, ObligationName}
import frflow.proof.reading.{Elaboration, TheoremVerdict}
import frflow.proof.verdict.*

/** One node's check: Lean's steps, each a build followed by a pure judge (`proof.verdict.Judge`) that may end the
  * check there. The model first (`Spec`); the proof file's rules and the shared lemmas; `complete` (by automation,
  * or the proof file), refuted on a case when it does not go through and its one part fixes an answer; `impl`; the
  * composition `holds`; then the checks module theorem by theorem (each obligation proven or not, each try shown or
  * not: a try Lean does not prove is an error there and shows nothing); and a root's `root_impl`. A module Lake did
  * not run (one it imports failed) proves nothing and shows nothing; a proof whose audit (`#print axioms`) Lean did
  * not print is not checked (fail closed). `Judge.node` ends a check that got through, on the axioms each proof that
  * went through rests on, `parts` the statuses of its parts.
  */
final class NodeChecker[F[_]: Monad: Clock](lake: Lake[F], files: ProjectFiles[F], refutations: Refutations[F]):
  private type Step[A] = EitherT[F, Judged, A]
  /** Outcomes, and the axioms the proven ones rest on. */
  private type Judging = (List[Result], List[String])
  private val none: Step[Judging] = EitherT.pure((Nil, Nil))

  def apply(a: Analysis, n: NodeId, parts: List[CheckStatus]): F[NodeCheck] =
    val lean = NodeLean(a, n)
    val steps: Step[Judged] =
      for
        _             <- run(lean.module(NodePart.Spec)).flatMap(r => stop(Judge.model(r)))
        _             <- proofFile(lean)
        (done, found) <- complete(lean, a)
        impl          <- proven(lean, ObligationName.Impl)
        holds         <- composed(lean, done)
        checks        <- checked(lean)
        root          <- rootImpl(lean)
      yield
        val (results, axioms) = (done ++ impl._1 ++ checks._1 ++ root._1, holds ++ impl._2 ++ checks._2 ++ root._2)
        val j = Judge.node(results, axioms, parts)
        // A step Lean refutes on a case is false, not open.
        val refuted = found.exists { case Finding.StepRefuted(_) => true; case _ => false }
        j.copy(status = if refuted then CheckStatus.Failed else j.status, findings = j.findings ++ found)
    steps.merge.flatMap(j => Clock[F].realTimeInstant.map(NodeCheck(n, a.keys.node(n), j.status, j.results,
      j.findings, _)))

  private def stop(j: Option[Judged]): Step[Unit] = EitherT.fromEither(j.toLeft(()))

  /** A build: Lean's output, or the check ended when it timed out. */
  private def run(m: ModuleName): Step[ProverRun] =
    EitherT(lake.build(NonEmptyList.one(m)).map {
      case ProverRun.TimedOut(_) => Left(Judged(CheckStatus.Timeout, Nil, List(Finding.LeanTimedOut)))
      case done                  => Right(done)
    })

  /** The proof file: only what one may contain; the shared lemmas it imports, built with no `sorry`. */
  private def proofFile(lean: NodeLean): Step[Unit] = lean.proof.fold(EitherT.pure[F, Judged](())) { f =>
    stop(Judge.proofFile(f)) >> lean.lemmas.fold(EitherT.pure[F, Judged](()))(l =>
      run(lean.layout.lemmas).flatMap(r => stop(Judge.lemmas(l, r))))
  }

  /** `complete`, and when neither automation nor the developer's proof proves it, a case Lean proves refutes the
    * step.
    */
  private def complete(lean: NodeLean, a: Analysis): Step[(List[Result], List[Finding])] =
    lean.required(ObligationName.Complete).fold(EitherT.pure[F, Judged]((List.empty[Result], List.empty[Finding]))) {
      o =>
        val authored = o.discharge == Discharge.Authored
        val module = if authored then lean.layout.proofs(lean.node) else lean.module(NodePart.Auto)
        run(module).flatMap { r =>
          val result = judged(o, if authored then lean.elaboratedProof(r) else lean.elaborated(NodePart.Auto, r))
          if result.status == ObligationStatus.Proven then EitherT.pure((List(result), Nil))
          else EitherT.liftF(refuted(lean, a).map(f => (List(result), f.toList)))
        }
    }

  /** A case refuting the step, searched for now, which Lean proves refutes it. */
  private def refuted(lean: NodeLean, a: Analysis): F[Option[Finding]] =
    refutations.of(a, lean.node).flatMap(_.flatTraverse { found =>
      val m = lean.refutes(found)
      files.writeIfChanged(m.name.file, Print.module(m)) >> lake.build(NonEmptyList.one(m.name)).map(r =>
        Option.when(lean.elaborated(m, r).exists(_.verdict("refutes") == TheoremVerdict.Proven))(
          Finding.StepRefuted(found.inputs)))
    })

  /** `impl`, in a module of its own, with the axioms its proof rests on when it goes through. */
  private def proven(lean: NodeLean, name: ObligationName): Step[Judging] =
    lean.required(name).filter(_ => lean.has(NodePart.Impl)).fold(none)(o =>
      run(lean.module(NodePart.Impl)).map(r => audited(lean, o, lean.elaborated(NodePart.Impl, r))))

  /** `holds`, composed once `complete` is proven, with the axioms it rests on: a composition Lean does not build
    * fails the check.
    */
  private def composed(lean: NodeLean, done: List[Result]): Step[List[String]] =
    if !lean.has(NodePart.Theorems) || !done.forall(_.status == ObligationStatus.Proven) then EitherT.pure(Nil)
    else run(lean.module(NodePart.Theorems)).flatMap { r =>
      val e = lean.elaborated(NodePart.Theorems, r)
      r match
        case ProverRun.Failed(_) => EitherT.leftT(Judged(CheckStatus.Failed, done,
          List(Finding.NotProven(e.toList.flatMap(_.diagnostics.filter(_.error))))))
        case _                   => e.flatMap(_.axiomsOf("holds")).fold(
          EitherT.leftT[F, List[String]](Judged(CheckStatus.Open, done, List(Finding.NotProven(Nil)))))(
          EitherT.pure(_))
    }

  /** The checks module, theorem by theorem: each other obligation, each try. */
  private def checked(lean: NodeLean): Step[Judging] =
    if !lean.has(NodePart.Checks) then none
    else run(lean.module(NodePart.Checks)).map { r =>
      val e = lean.elaborated(NodePart.Checks, r)
      val others = lean.others.map(o => audited(lean, o, e))
      val tries = lean.tried.map(o => e.fold(Result(o.name, ObligationStatus.NotShown, Nil))(Judge.tried(o.name, _)))
      (others.flatMap(_._1) ++ tries, others.flatMap(_._2))
    }

  /** A root's `root_impl`: proven when Lean proves it, with the axioms it rests on. */
  private def rootImpl(lean: NodeLean): Step[Judging] =
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

  /** An obligation judged where Lean ran on it; not checked where it did not. */
  private def judged(o: Obligation, e: Option[Elaboration]): Result =
    e.fold(Result(o.name, ObligationStatus.Unchecked, Nil))(Judge.required(o.name, _))

  /** Proven only with the axioms its audit lists (fail closed): one Lean says nothing of is not checked. */
  private def audited(lean: NodeLean, o: Obligation, e: Option[Elaboration]): Judging =
    val result = judged(o, e)
    val audit = e.flatMap(_.axiomsOf(lean.named(o)))
    if result.status != ObligationStatus.Proven then (List(result), Nil)
    else audit.fold((List(result.copy(status = ObligationStatus.Unchecked)), Nil))(as => (List(result), as))
