package frflow.wire

import frflow.core.name.NodeId
import java.time.Instant
import org.scalacheck.Gen

/** What every generator of the files draws from: texts with what JSON escapes (quotes, backslashes, newlines,
  * control characters) and characters beyond ASCII, names, instants to the nanosecond.
  */
object Draws:
  private val pieces = List("a", "Oak", "booked", " ", "  ", "\"", "\\", "\n", "\t", "\r", "\u0001", "é", "中", "😀",
    "_", "1", "{", "}", ":", ",")

  val text: Gen[String] = Gen.choose(0, 8).flatMap(n => Gen.listOfN(n, Gen.oneOf(pieces))).map(_.mkString)
  val word: Gen[String] = Gen.choose(1, 4).flatMap(n => Gen.listOfN(n, Gen.oneOf("a", "B", "x", "_", "1", "é")))
    .map(_.mkString)
  val node: Gen[NodeId] = word.map(NodeId(_))
  val hex: Gen[String] = Gen.listOfN(16, Gen.hexChar).map(_.mkString.toLowerCase)
  val instant: Gen[Instant] =
    Gen.zip(Gen.choose(0L, 4102444800L), Gen.choose(0L, 999999999L)).map(Instant.ofEpochSecond(_, _))

  def few[A](g: Gen[A]): Gen[List[A]] = Gen.choose(0, 3).flatMap(Gen.listOfN(_, g))

  /** A map from distinct keys, drawn as pairs. */
  def byKey[K, V](key: Gen[K], value: Gen[V]): Gen[Map[K, V]] = few(Gen.zip(key, value)).map(_.toMap)
