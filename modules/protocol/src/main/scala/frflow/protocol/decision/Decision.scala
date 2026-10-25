package frflow.protocol
package decision

import JsonDefaults.given
import io.circe.derivation.ConfiguredCodec
import java.time.Instant

/** A decision of the developer about a node, bound to the hash of its `content` as they saw it, and to
  * the meaning of what it rested on (`chain`). `after` is the decision it follows (see `forked`).
  */
final case class Decision(action: Action, by: String, at: Instant, reason: String, rejected: List[NodeId] = Nil,
    after: Option[EntryRef] = None, code: Option[Fingerprint] = None, commit: Option[String] = None,
    key: Option[KeyId] = None, sig: Option[String] = None, chain: Chain = Chain.empty,
    content: Content = Content.empty) derives ConfiguredCodec:
  def hash: Hash = content.hash
  def unsigned: Decision = copy(key = None, sig = None)
