package frflow.dsl.flow

import frflow.dsl.term.Term

/** A boundary of the tests, its operations derived (`derives BoundaryOps`). */
trait Store[F[_], T[_]] derives BoundaryOps:
  def load: F[T[BigInt]]
  def save(n: T[BigInt]): F[Unit]

object Store:
  val store: Boundary[Store] = Boundary[Store]("a number the tests keep")
  val recording: Store[Recorded, Term] = store.recording

  /** FrFlow's clock, its operations derived here: the DSL's own module cannot expand its macro. */
  private given BoundaryOps[Clock] = BoundaryOps.derived
  val clock: Clock[Recorded, Term] = Boundary[Clock]("the time").recording
