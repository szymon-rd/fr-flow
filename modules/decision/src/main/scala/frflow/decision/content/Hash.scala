package frflow.decision.content

import cats.{Eq, Show}

/** The hash of a content as the developer decided it (whitespace runs counted as one space). */
opaque type Hash = String

object Hash:
  def apply(sha: String): Hash = sha
  extension (h: Hash) def value: String = h
  given Eq[Hash] = Eq.fromUniversalEquals
  given Show[Hash] = Show.show(identity)
