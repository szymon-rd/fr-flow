package frflow.project.port

import cats.Monad
import cats.effect.Ref
import cats.syntax.all.*
import frflow.core.name.RelPath

/** The project's files in memory: the checker and the programs tested without a disk. `all` is what is held now. */
final class MemoryFiles[F[_]: Monad] private (held: Ref[F, Map[RelPath, String]]) extends ProjectFiles[F]:
  def read(p: RelPath): F[Option[String]] = held.get.map(_.get(p))
  def list(dir: RelPath): F[List[RelPath]] = held.get.map(_.keys.filter(p => p != dir && p.isUnder(dir)).toList.sorted)
  def writeIfChanged(p: RelPath, text: String): F[Boolean] =
    held.modify(m => if m.get(p).contains(text) then (m, false) else (m.updated(p, text), true))
  def delete(p: RelPath): F[Unit] = held.update(_ - p)
  def all: F[Map[RelPath, String]] = held.get

object MemoryFiles:
  def apply[F[_]: Monad: Ref.Make](start: Map[RelPath, String]): F[MemoryFiles[F]] =
    Ref.of[F, Map[RelPath, String]](start).map(new MemoryFiles(_))
