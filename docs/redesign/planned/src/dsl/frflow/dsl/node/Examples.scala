package frflow.dsl.node

import frflow.core.example.{CallExample, RunExample}
import frflow.dsl.build.Deferred

/** Examples as written, reified against the operation's type when elaborated. */
object Examples:
  def calls[F](head: Head, givens: List[Binding], cases: List[Case[F]]): Deferred[List[CallExample]] = ???
  def runs[F](head: Head, givens: List[Binding], cases: List[Case[F]]): Deferred[List[RunExample]] = ???
