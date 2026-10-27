package frflow.decision.content

import java.nio.charset.StandardCharsets.UTF_8
import java.security.MessageDigest

/** SHA-256 of text, in hex: the one hash every content, chain and fingerprint is made with. */
object Sha:
  def apply(s: String): String =
    MessageDigest.getInstance("SHA-256").digest(s.getBytes(UTF_8)).map(b => f"${b & 0xff}%02x").mkString
  /** The hash of several parts, joined by NUL (as every recorded chain and check hash was made). */
  def parts(ps: String*): String = apply(ps.mkString("\u0000"))
