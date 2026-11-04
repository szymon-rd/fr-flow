package frflow.decision.content

import java.nio.charset.StandardCharsets.UTF_8
import java.security.MessageDigest

/** SHA-256 of text, in hex: the one hash every content, chain and fingerprint is made with. */
object Sha:
  def apply(s: String): String = bytes(s.getBytes(UTF_8))
  def bytes(b: Array[Byte]): String =
    MessageDigest.getInstance("SHA-256").digest(b).map(x => f"${x & 0xff}%02x").mkString
  /** The hash of several parts, joined by NUL (as every recorded chain and check hash was made). */
  def parts(ps: String*): String = apply(ps.mkString("\u0000"))
