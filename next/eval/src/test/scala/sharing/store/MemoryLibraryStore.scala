package sharing.store

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import sharing.domain.Library

/** The library kept in memory: the store's Scala for development and tests, tested against `libraryModel`. Each call
  * takes the next of the faults it is given (`true`: that call fails, as a store not answering does, and changes
  * nothing), and succeeds when none is left.
  */
final class MemoryLibraryStore private (held: Ref[IO, Library], faults: Ref[IO, List[Boolean]]):
  def load: IO[Library] = up *> held.get
  def save(library: Library): IO[Unit] = up *> held.set(library)
  def library: IO[Library] = held.get
  /** The faults the next calls take, in order. */
  def failing(fs: List[Boolean]): IO[Unit] = faults.set(fs)

  private def up: IO[Unit] = faults.modify {
    case f :: rest => (rest, f)
    case Nil       => (Nil, false)
  }.flatMap(f => IO.raiseError(IllegalStateException("the store is down")).whenA(f))

object MemoryLibraryStore:
  def holding(library: Library): IO[MemoryLibraryStore] =
    (Ref[IO].of(library), Ref[IO].of(List.empty[Boolean])).mapN(MemoryLibraryStore(_, _))
