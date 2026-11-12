package frflow.project.port

import cats.data.NonEmptyList
import frflow.proof.lean.ast.ModuleName
import frflow.proof.verdict.ProverRun

/** The prover in the project's `rocq/`: whether it runs, and a build of modules, with its report of every file it
  * read for them (`proof.reading.RocqReport`). A module is run only when every module it imports went through whole;
  * a lemma of it Rocq does not accept is reported and given up, so the rest of the module is still read.
  * Interpreters: the live one (`rocq.RocqProver`: `rocq compile`, one build at a time), and a scripted one answering
  * by module (`ScriptedProver`), which tests the check's planning, caching and judges without Rocq.
  */
trait Prover[F[_]]:
  def available: F[Boolean]
  def build(targets: NonEmptyList[ModuleName]): F[ProverRun]
