package frflow.web

import java.nio.charset.StandardCharsets.UTF_8
import java.security.MessageDigest

/** What a request passes through: the session's token (only the browser opened from the printed link has it, not an
  * agent's process on this machine), and the model's fingerprint when `serve` started (deciding is refused once it
  * moves: what is on disk is no longer what this process compiled).
  */
final case class Gate(token: String, started: String):
  def admits(offered: Option[String]): Boolean =
    offered.exists(t => MessageDigest.isEqual(t.getBytes(UTF_8), token.getBytes(UTF_8)))
