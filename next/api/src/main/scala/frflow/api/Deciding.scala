package frflow.api

import frflow.api.view.Decided
import frflow.decision.rules.{Command, Refusal}

/** What a front end decides with: who decides (`as`, else `FRFLOW_AS`, else the name the developer's key is listed
  * under in the committed deciders' list), what a decision would record, and recording it, signed. Laws: `preview`
  * records nothing and gives what `decide` then records; a refused decision records nothing.
  */
trait Deciding[F[_]]:
  def developer(as: Option[String]): F[Either[Refusal, String]]
  def preview(c: Command, by: String): F[Either[Refusal, Decided]]
  def decide(c: Command, by: String): F[Either[Refusal, Decided]]
