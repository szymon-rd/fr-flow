package frflow.api

import frflow.api.view.diff.NodeDiff
import frflow.api.view.source.Sources
import frflow.api.view.vocab.Vocab
import frflow.api.view.{Found, View}
import frflow.core.name.NodeId
import frflow.decision.ledger.Decision

/** What a front end reads: the view, a node's diff since its decision (none when the model has no such node), what a
  * node is written in (its code and its Lean, none likewise), the model's words, where a change belongs, and the
  * model's fingerprint (the sources as they are now: a process that keeps running compiled its model when it
  * started, and once this moves what it shows is not decided on), and the decisions as the ledger holds them, by node
  * (read from disk, whatever model this process compiled: what an agent waiting on the developer watches). Laws:
  * reading changes nothing; `diff(id)` and `sources(id)` are defined exactly for the nodes of `view`.
  */
trait Reading[F[_]]:
  def view: F[View]
  def diff(id: NodeId): F[Option[NodeDiff]]
  def sources(id: NodeId): F[Option[Sources]]
  def vocabulary: F[Vocab]
  def find(query: String): F[Found]
  def modelFingerprint: F[String]
  def decisions: F[Map[NodeId, List[Decision]]]
