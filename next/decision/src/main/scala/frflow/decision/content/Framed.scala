package frflow.decision.content

import java.nio.ByteBuffer

/** Fields made into the bytes a signature or a reference covers, so that no two lists of fields give the same bytes:
  * each field is written as its length, a colon, then itself, every character as its two UTF-16 bytes (lossless for
  * any string, which UTF-8 is not for a lone surrogate). A reason holding a NUL, or an id holding a comma, cannot
  * make one decision's bytes another's.
  */
object Framed:
  def apply(fields: List[String]): Array[Byte] =
    val text = fields.map(f => s"${f.length}:$f").mkString
    val bytes = ByteBuffer.allocate(text.length * 2)
    text.foreach(c => bytes.putChar(c): Unit)
    bytes.array
