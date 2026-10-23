package frflow
package check

import cats.data.{EitherT, NonEmptyList}
import cats.effect.{IO, Resource}
import cats.effect.syntax.all.*
import cats.syntax.all.*
import frflow.lean.{Elaboration, Generate, LeanOutput, LeanSource, ProofFiles}
import frflow.ledger.Store
import frflow.protocol.*
import frflow.protocol.ObligationName.{Complete, Impl}
import io.circe.syntax.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** What to check, in what order: each node after what its Lean imports, a level's nodes side by side; `only`: that node alone. */
final case class CheckPlan(a: Analysis, only: Option[String]):
  private val g = a.generate
  private val kb = a.kb

  val todo: List[Node[?]] = kb.ordered.filter(g.formal).filter(n => only.forall(_ == n.id))
  def unchanged(n: Node[?]): Option[NodeCheck] = a.current(n).filter(_ => only.isEmpty)
  val pending: List[Node[?]] = todo.filter(unchanged(_).isEmpty)

  /** By level: one more than the highest below it. */
  val levels: List[List[Node[?]]] =
    def below(n: Node[?]): List[Node[?]] =
      (kb.parts(n) ++ g.callees(n) ++ (if kb.isRoot(n) then kb.nodes.filter(c => g.provenImpl(c).isDefined) else Nil))
        .filter(x => g.formal(x) && !(x eq n))
    def go(n: Node[?], seen: Set[String], known: Map[String, Int]): (Int, Map[String, Int]) =
      known.get(n.id).fold {
        val (l, after) = below(n).filterNot(x => seen(x.id)).foldLeft((0, known)) { case ((l, k), x) =>
          val (lx, k2) = go(x, seen + n.id, k)
          (l.max(lx + 1), k2)
        }
        (l, after.updated(n.id, l))
      }(l => (l, known))
    val level = todo.foldLeft(Map.empty[String, Int])((known, n) => go(n, Set.empty, known)._2)
    todo.groupBy(n => level.getOrElse(n.id, 0)).toList.sortBy(_._1).map(_._2)

  /** The models, and the proofs of the code (which import only models), first in one build: one at a time, they were most of a cold check. */
  val prebuild: List[String] =
    val ready = pending.filter(g.waitsForDefinition(_).isEmpty)
    ready.map(n => g.layout.spec(n.id).name) ++ ready.filter(g.obligation(_, ObligationName.Impl).isDefined).map(n => g.layout.impl(n.id).name)

  /** A level's theorems, in one build. */
  def theorems(level: List[Node[?]]): List[String] =
    level.filter(n => unchanged(n).isEmpty && g.waitsForDefinition(n).isEmpty).map(n => g.layout.theorems(n.id).name)

  /** The status of a node's formal parts, from this run or the record. */
  def parts(n: Node[?], done: Map[String, NodeCheck]): List[(String, Option[CheckStatus])] =
    kb.parts(n).filter(g.formal).map(p => p.id -> done.get(p.id).orElse(a.current(p)).map(_.status))

  /** A node is proven with its parts: kept as it was only while they all are. */
  def kept(n: Node[?], parts: List[(String, Option[CheckStatus])]): Option[NodeCheck] =
    unchanged(n).filter(_ => parts.forall(_._2.contains(CheckStatus.Proven)))

/** How far a check is: Lean is about to build the models (`level` 0), or to prove level `level` of `levels`. */
final case class Progress(level: Int, levels: Int, nodes: List[String])

/** Writes the Lean and the snapshot, and checks: a plan run level by level, each level's nodes side by side. */
object CheckRunner:
  /** Writes the generated Lean; returns the files that changed. */
  def render(a: Analysis): IO[List[String]] =
    val ws = a.ws
    val keep = a.files.keySet.map(ws.lean.resolve(_).normalize)
    for
      _ <- Disk.update(ws.lean.resolve("lakefile.toml"), a.generate.lakefile(ws.kernelPath))
      _ <- Disk.update(ws.lean.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
      changed <- a.files.toList.sortBy(_._1).parTraverseN(8)((rel, text) => Disk.update(ws.lean.resolve(rel), text).map(Option.when(_)(rel)))
      stale <- a.generate.layout.generatedDirs.map(ws.lean.resolve).flatTraverse(d => Disk.isDirectory(d).ifM(Disk.files(d), IO.pure(Nil)))
      _ <- stale.filterNot(p => keep(p.normalize)).traverse_(Disk.delete)
    yield changed.flatten

  def writeSnapshot(a: Analysis): IO[Path] = Store.writeJson(a.ws.snapshotFile, a.snapshot.asJson).as(a.ws.snapshotFile)

  /** Renders, checks nodes (all, or one), parts first, and records the results: the nodes checked, and the analysis then. */
  def check(a: Analysis, lake: Lake, cfg: Config, only: Option[String],
      progress: Progress => IO[Unit] = _ => IO.unit): IO[(List[(Node[?], NodeCheck)], Analysis)] =
    val plan = CheckPlan(a, only)
    // A batch that builds is built for each of its targets: their own builds are skipped (one at a time, they cost
    // about as much as Lean's start). Each node's own build then replays it, with its messages.
    def batch(targets: List[String]): IO[Set[String]] =
      NonEmptyList.fromList(targets).filter(_.size > 1)
        .fold(IO.pure(Set.empty[String]))(ts => lake.build(ts).map(r => if r.ok then targets.toSet else Set.empty))
    val levels = plan.levels.filter(_.exists(plan.unchanged(_).isEmpty))
    for
      _ <- render(a)
      _ <- progress(Progress(0, levels.size, Nil)).whenA(plan.prebuild.nonEmpty)
      pre <- batch(plan.prebuild)
      (done, _) <- plan.levels.foldLeftM((Map.empty[String, NodeCheck], pre)) { case ((done, built), level) =>
        val step = levels.indexOf(level) + 1
        progress(Progress(step, levels.size, level.filter(plan.unchanged(_).isEmpty).map(_.id))).whenA(step > 0) *>
        batch(plan.theorems(level)).map(built ++ _).flatMap { built =>
          val checker = NodeChecker(a, lake, built)
          level.parTraverseN(cfg.threads) { n =>
            val parts = plan.parts(n, done)
            plan.kept(n, parts).fold(checker.check(n, parts))(IO.pure).tupleLeft(n.id)
          }.map(rs => (done ++ rs, built))
        }
      }
      results = plan.todo.flatMap(n => done.get(n.id).map(n -> _))
      all = a.checks.filter((id, _) => a.kb.node(id.value).isDefined) ++ results.map((n, c) => NodeId(n.id) -> c)
      _ <- Inputs.saveChecks(a.ws.checksFile, all)
    yield (results, a.withChecks(all))

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
      root <- lift(g.rootImpl.filter(_ => a.kb.isRoot(n)).traverse(_ => generated(g.layout.rootImpl.path)))
    yield Verdict.finish(a, n, results, impl, checks, root)

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

/** The goal an obligation leaves after a proof's first steps (`ProofFiles.recipe`): what `scaffold` stubs and `check` prints. */
object ProofState:
  /** The goal, or none when Lean cannot say. */
  def of(lake: Lake, g: Generate, n: Node[?], o: ObligationName): IO[Option[String]] =
    Resource.make(IO.blocking(Files.createTempFile("frflow-state", ".lean")))(f => IO.blocking(Files.deleteIfExists(f)).void).use { file =>
      IO.blocking(Files.writeString(file, g.goalFile(n, o), UTF_8)) *>
        lake.elaborate(file.toString).map(goal(_, file.getFileName.toString))
    }

  /** What Lean said of that file: the unsolved goals, or that the steps prove it. */
  def goal(run: Run, fileName: String): Option[String] =
    val errs = LeanOutput.diagnostics(run.output).filter(d => d.isError && d.file.endsWith(fileName))
    errs.find(_.message.startsWith("unsolved goals")).map(_.message.stripPrefix("unsolved goals").trim)
      .orElse(Option.when(errs.isEmpty && run.ok)("no goals: these steps prove it"))

  def text(o: ObligationName, state: String): String =
    s"After `${ProofFiles.recipe(o).mkString("; ")}` (the first steps the stub has), the goal is:\n$state"

/** Creates the proof file of a node with a stub for each obligation the last check left open. */
object Scaffold:
  /** The proof file written (its path under the project), or none when there was nothing to add. */
  def apply(a: Analysis, lake: Lake, n: Node[?]): IO[Option[String]] =
    val g = a.generate
    val rel = g.layout.proofs(n.id).path
    val add = stubs(a, n)
    // Each stub shows, as a comment, the goal its first steps leave: the state `check` prints.
    val states: IO[Map[ObligationName, Option[String]]] =
      lake.available.ifM(lake.build(g.layout.spec(n.id).name).map(_.ok), IO.pure(false))
        .flatMap(built => if !built then IO.pure(Map.empty) else add.traverse(o => ProofState.of(lake, g, n, o).tupleLeft(o)).map(_.toMap))
    def comment(st: String) =
      s"  /- The goal here (as `check` prints it when automation gives up):\n${st.replace("-/", "- /").linesIterator.map("     " + _).mkString("\n")}\n  -/\n"
    // The proof file with the stubs added (created if missing); none when its end is not found.
    def text(state: ObligationName => String) = a.proofOf(n) match
      case None => Some(g.proofFile(n, add, state))
      case Some(src) =>
        val i = src.lastIndexOf(s"end ${a.kb.name}.${n.id}.Proofs")
        Option.when(i >= 0)(src.substring(0, i) + g.stubs(add, state) + src.substring(i))
    if add.isEmpty then IO.pure(None)
    else states.flatMap(st => text(o => st.get(o).flatten.fold("")(comment))
      .traverse(t => Disk.update(a.ws.lean.resolve(rel), t)).map(_.filter(identity).map(_ => s"lean/$rel")))

  /** Those the last check left open, or `complete` before any check; less those the proof file has. */
  def stubs(a: Analysis, n: Node[?]): List[ObligationName] =
    val g = a.generate
    val names = g.obligations(n).map(_.name)
    val last = a.checks.get(NodeId(n.id))
    val open = last.toList.flatMap(_.obligations)
      .filter(r => r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed).map(_.name).filter(names.contains)
    val wanted = if last.isDefined then open else g.obligation(n, ObligationName.Complete).map(_.name).toList
    val existing = a.proofOf(n).fold(List.empty[String])(src => LeanSource.theorems(src).map(_.name))
    wanted.filterNot(o => existing.contains(o.lean))
