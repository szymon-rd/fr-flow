package whole

import frflow.core.analysis.{Problem, Resolve, Resolved, Validate}
import frflow.core.{Elaborated, Theory}
import frflow.dsl.build.ElabError
import frflow.dsl.kb.FrModel

/** A FrModel as the analyses read it: elaborated, validated and resolved, or what stopped it. */
object Theories:
  def errors(kb: FrModel): List[ElabError] = kb.elaborated.fold(_.iterator.toList, _ => Nil)

  def elaborated(kb: FrModel): Elaborated =
    kb.elaborated.fold(es => throw AssertionError(es.iterator.mkString("\n")), identity)

  def theory(kb: FrModel): Theory = elaborated(kb).theory

  def problems(kb: FrModel): List[Problem] = Validate(elaborated(kb)).fold(_.iterator.toList, _ => Nil)

  def resolved(kb: FrModel): Resolved =
    Resolve(Validate(elaborated(kb)).fold(ps => throw AssertionError(ps.iterator.mkString("\n")), identity))
