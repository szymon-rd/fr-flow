package frflow.proof.terms

import frflow.core.code.Code
import frflow.core.name.SymbolName
import frflow.core.Theory
import frflow.core.vocab.Define

/** What a reading of proven code for its calls knows of the Definitions it calls: those given plain Scala, whose
  * arguments are checked at the call (`scala`); and those whose proven code is a define, read in place on the
  * arguments they are given (`proven`, owner §37: a value handed on through proven code reaches the plain Scala it
  * calls).
  */
final case class Covered(scala: Set[SymbolName], proven: Map[SymbolName, Define])

object Covered:
  def of(t: Theory): Covered = Covered(
    t.code.attached.collect { case (d, a) if a.code.scala.nonEmpty => d }.toSet,
    t.code.attached.toList.flatMap((d, a) => a.code match
      case Code.Proven(c) => t.vocabulary.define(c).map(d -> _)
      case _              => None).toMap)
