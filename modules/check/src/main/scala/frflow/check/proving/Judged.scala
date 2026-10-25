package frflow
package check
package proving

import frflow.protocol.*
import java.time.Instant

/** What a check of a node finds, before it is stamped with its hash and time. */
final case class Judged(status: CheckStatus, results: List[Result], messages: List[String], axioms: List[String] = Nil,
    hint: Option[String] = None):
  def withEvaluations(rs: List[Result]): Judged = copy(results = results ++ rs)
  def stamp(hash: Hash, at: Instant): NodeCheck = NodeCheck(hash, status, results, messages, axioms, at, hint)
