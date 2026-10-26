package frflow.api

import frflow.decision.rules.{Command, Refusal}
import frflow.project.program.Decided

/** What a front end decides with: who decides, what a decision would record, and recording it. */
trait Deciding[F[_]]:
  def developer(as: Option[String]): F[Either[Refusal, String]]
  def preview(c: Command, by: String): F[Either[Refusal, Decided]]
  def decide(c: Command, by: String): F[Either[Refusal, Decided]]
