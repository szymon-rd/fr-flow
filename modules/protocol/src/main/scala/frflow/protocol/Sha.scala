package frflow.protocol

/** SHA-256, in hex: what every hash in FrFlow is. */
object Sha:
  def bytes(b: Array[Byte]): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(b).map("%02x".format(_)).mkString
  def apply(s: String): String = bytes(s.getBytes(java.nio.charset.StandardCharsets.UTF_8))
  def parts(ps: String*): String = apply(ps.mkString("\u0000"))
