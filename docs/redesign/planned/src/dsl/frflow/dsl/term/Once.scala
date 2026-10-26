package frflow.dsl.term

import java.util.concurrent.atomic.AtomicReference

/** A value computed on first use and kept: a define's compiled Scala. Two threads may both compute it; the first kept
  * stays.
  */
final class Once[A]:
  private val cell = AtomicReference[Option[A]](None)

  def get(make: => A): A =
    cell.get.getOrElse(cell.updateAndGet(_.orElse(Some(make))).getOrElse(make))

  /** The value, if computed yet. */
  def held: Option[A] = cell.get
