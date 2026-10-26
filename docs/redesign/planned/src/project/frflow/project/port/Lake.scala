package frflow.project.port

import cats.data.NonEmptyList
import cats.effect.{Async, Resource}
import frflow.proof.lean.ast.ModuleName
import frflow.proof.verdict.ProverRun

/** Lean's build tool. Interpreters: the live one (a pool of `lake` processes with timeouts, a `Resource`), and a
  * scripted one answering by module, which tests the check's planning, caching and judges without Lean.
  */
trait Lake[F[_]]:
  def available: F[Boolean]
  def build(targets: NonEmptyList[ModuleName]): F[ProverRun]
  def elaborate(file: ModuleName): F[ProverRun]

object Lake:
  def make[F[_]: Async](leanDir: java.nio.file.Path, threads: Int): Resource[F, Lake[F]] = ???
