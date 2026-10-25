package frflow
package check
package proving

import cats.data.{EitherT, NonEmptyList}
import cats.effect.IO
import cats.syntax.all.*
import frflow.lean.Elaboration
import frflow.protocol.*
import frflow.protocol.ObligationName.{Complete, Impl}

/** Checks one node against Lean: each step runs Lean, then a pure judge (`Verdict`) says whether the check ends there (a `Left`). */
final class NodeChecker(a: Analysis, lake: Lake, prebuilt: Set[String]):
  private type Step[A] = EitherT[IO, Judged, A]
  private val g = a.generate
  private def lift[A](io: IO[A]): Step[A] = EitherT.liftF(io)
  private def stop(j: Option[Judged]): Step[Unit] = EitherT.fromEither(j.toLeft(()))
  private def build(target: String): IO[Run] = if prebuilt(target) then IO.pure(Run.built) else lake.build(target)
  private def elaborate(rel: String, src: String): IO[Elaborated] = lake.elaborate(rel).map(r => Elaborated(r, Elaboration(src, r.output, rel)))
  private def generated(rel: String): IO[Elaborated] = elaborate(rel, a.files.getOrElse(rel, ""))
  private def state(n: Node[?], o: ObligationName): IO[Option[String]] = ProofState.of(lake, g, n, o)

  def check(n: Node[?], parts: List[(String, Option[CheckStatus])]): IO[NodeCheck] =
    val proof = a.proofOf(n).getOrElse("")
    val steps = for
      _ <- stop(Verdict.waiting(a.kb, g, n))
      _ <- lift(build(g.layout.spec(n.id).name)).flatMap(r => stop(Verdict.model(r)))
      _ <- lemmas(proof)
      evaluated <- evaluate(n)
      j <- proven(n, proof, parts).bimap(_.withEvaluations(evaluated), _.withEvaluations(evaluated))
    yield j
    steps.merge.flatMap(j => IO.realTimeInstant.map(j.stamp(a.checkHash(n), _)))

  // Lemmas shared by the proof files: the same filter, built.
  private def lemmas(proof: String): Step[Unit] =
    EitherT.fromEither[IO](Verdict.lemmas(g, proof, a.inputs.proofs.get("Lemmas"))).flatMap { needed =>
      if !needed then EitherT.pure(()) else lift(lake.build(g.layout.lemmas.name)).flatMap(r => stop(Verdict.lemmasBuilt(g, r)))
    }

  // The examples, evaluated in Lean: every result carries them.
  private def evaluate(n: Node[?]): Step[List[Result]] =
    val (evals, notEvaluated) = g.evals(n)
    lift(if evals.isEmpty then IO.pure(None) else generated(g.layout.eval(n.id).path).map(Some(_)))
      .map(Verdict.evaluations(evals, notEvaluated, _))
      .flatTap(rs => stop(Verdict.agree(n, rs)))

  private def proven(n: Node[?], proof: String, parts: List[(String, Option[CheckStatus])]): Step[Judged] =
    for
      split <- lift(complete(n))
      impl <- lift(implementation(n, proof))
      results = split ++ impl.map(_._1)
      _ <- stop(Verdict.obligations(g, n, split, results, parts))
      _ <- lift(build(g.layout.theorems(n.id).name)).flatMap(r => stop(Verdict.theorems(results, r)))
      _ <- proofFile(n, proof, results)
      checks <- lift(generated(g.layout.checks(n.id).path))
      _ <- stop(Verdict.checksRan(results, checks.run))
      root <- lift(g.rootImpl.filter(_ => a.kb.isRoot(n)).traverse(_ => rootImpl))
    yield Verdict.finish(a, n, results, impl, checks, root)

  // `root_impl` composes the proofs of the code; `lake env lean` builds nothing it imports, so they are built first:
  // else it reads what an earlier build left of them, or nothing. One that does not build is the reason, by name.
  private def rootImpl: IO[Either[String, Elaborated]] =
    val rel = g.layout.rootImpl.path
    val composed = Verdict.composed(a.kb, g, a.files.getOrElse(rel, ""))
    NonEmptyList.fromList(composed.map(c => g.layout.impl(c.id).name).filterNot(prebuilt))
      .fold(IO.pure(Run.built))(lake.build)
      .flatMap(r => Verdict.composedBuilt(g, composed, r).fold(generated(rel).map(Right(_)))(why => IO.pure(Left(why))))

  // Built already (with its level), automatic `complete` is proven without elaborating it again. Automation is
  // tried only while no proof file proves it: what to do next comes first.
  private def complete(n: Node[?]): IO[List[Result]] =
    val authored = g.isAuthored(n, Complete)
    g.obligation(n, Complete).toList.traverse { o =>
      val prebuilt = if authored then IO.pure(false) else build(g.layout.theorems(n.id).name).map(_.ok)
      val judged =
        if authored then elaborate(g.layout.proofs(n.id).path, a.proofOf(n).getOrElse("")).map(Verdict.judge(o.name, _, true))
        else generated(g.layout.auto(n.id).path).map(Verdict.judge(o.name, _, false))
      prebuilt.ifM(IO.pure(Result(o.name, ObligationStatus.Proven, "auto")),
        judged.flatMap { r =>
          if authored || r.status != ObligationStatus.Open then IO.pure(r) else state(n, Complete).map(Verdict.gaveUp(g, n, r, _))
        })
    }

  // Its code meets it, from what the contracts it calls promise: with the axioms its build rests on.
  private def implementation(n: Node[?], proof: String): IO[Option[(Result, Option[List[String]])]] =
    val authored = g.isAuthored(n, Impl)
    g.obligation(n, Impl).traverse { _ =>
      Verdict.implRules(proof).filter(_ => authored).fold(lake.build(g.layout.impl(n.id).name).flatMap { r =>
        (if r.ok || authored then IO.pure(None) else state(n, Impl)).map(Verdict.impl(g, n, authored, r, _))
      })(r => IO.pure((r, Some(Nil))))
    }

  // The proof file, when it proves obligations of the Checks file: everything else imports it.
  private def proofFile(n: Node[?], proof: String, results: List[Result]): Step[Unit] =
    val why: IO[Option[String]] = Verdict.proofFile(g, n, proof) match
      case Left(bad) => IO.pure(Some(bad))
      case Right(false) => IO.pure(None)
      case Right(true) => lake.build(g.layout.proofs(n.id).name).map(Verdict.proofFileBuilt(g, n, _))
    lift(why).flatMap(w => stop(w.map(Verdict.proofFileFails(g, n, results, _))))
