package frflow.wire.check

import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.reading.ObligationNames as Names
import io.circe.{Codec, Decoder, Encoder}

/** An obligation, and a try, in a file: the name of its theorem (`proof.reading.ObligationNames`). */
object ObligationNames:
  def text(o: ObligationName): String = Names.text(o)
  def obligation(s: String): Option[ObligationName] = Names.read(s)

  given Codec[ObligationName] = codec("obligation", Names.read)(Names.text)
  given Codec[TryKind] = codec("try", Names.tryKind)(Names.text)

  private def codec[A](what: String, read: String => Option[A])(write: A => String): Codec[A] =
    Codec.from(Decoder.decodeString.emap(s => read(s).toRight(s"no $what $s")), Encoder.encodeString.contramap(write))
