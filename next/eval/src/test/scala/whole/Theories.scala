package whole

import frflow.core.analysis.{Problem, Resolve, Resolved, Validate}
import frflow.core.{Elaborated, Theory}
import frflow.dsl.build.ElabError
import frflow.dsl.kb.KnowledgeBase

/** A knowledge base as the analyses read it: elaborated, validated and resolved, or what stopped it. */
object Theories:
  def errors(kb: KnowledgeBase): List[ElabError] = kb.elaborated.fold(_.iterator.toList, _ => Nil)

  def elaborated(kb: KnowledgeBase): Elaborated =
    kb.elaborated.fold(es => throw AssertionError(es.iterator.mkString("\n")), identity)

  def theory(kb: KnowledgeBase): Theory = elaborated(kb).theory

  def problems(kb: KnowledgeBase): List[Problem] = Validate(elaborated(kb)).fold(_.iterator.toList, _ => Nil)

  def resolved(kb: KnowledgeBase): Resolved =
    Resolve(Validate(elaborated(kb)).fold(ps => throw AssertionError(ps.iterator.mkString("\n")), identity))
