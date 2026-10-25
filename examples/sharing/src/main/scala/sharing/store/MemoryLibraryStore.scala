package sharing.store

import frflow.*
import java.util.concurrent.atomic.AtomicReference
import sharing.domain.*

/** The library in memory: for development and tests. Tested against LibraryModel (LibraryKept). */
final class MemoryLibraryStore(initial: Library) extends LibraryStore:
  private val held = AtomicReference(initial)
  def library: Library = held.get
  def load = Flow.effect(held.get)
  def save(library: Term[Library]) = Flow.effect(library)(l => held.set(l))
