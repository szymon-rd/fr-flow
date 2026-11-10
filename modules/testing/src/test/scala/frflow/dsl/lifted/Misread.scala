package frflow.dsl.lifted

/** Lifted code as a reader that misread its Scala would have made it: one function's term with another's Scala.
  * What `Agreement` must find; made here, in the reader's package, since `lifted` alone makes lifted code.
  */
object Misread:
  def of[A, R](term: Lifted.Of1[A, R], scala: A => R): Lifted.Of1[A, R] = Lifted.Of1(term, scala)
  def of[A, B, R](term: Lifted.Of2[A, B, R], scala: (A, B) => R): Lifted.Of2[A, B, R] = Lifted.Of2(term, scala)
