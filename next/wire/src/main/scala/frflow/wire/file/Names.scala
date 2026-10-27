package frflow.wire.file

import frflow.core.name.{BoundaryName, CtorName, DefName, ModelName, NodeId, OpName, SymbolName, TypeName}
import io.circe.{Codec, Decoder, Encoder}

/** The IR's names, each written as its text. */
object Names:
  private def text[A](make: String => A)(value: A => String): Codec[A] =
    Codec.from(Decoder.decodeString.map(make), Encoder.encodeString.contramap(value))

  given Codec[NodeId] = text(NodeId(_))(_.value)
  given Codec[SymbolName] = text(SymbolName(_))(_.value)
  given Codec[DefName] = text(DefName(_))(_.value)
  given Codec[ModelName] = text(ModelName(_))(_.value)
  given Codec[CtorName] = text(CtorName(_))(_.value)
  given Codec[TypeName] = text(TypeName(_))(_.value)
  given Codec[BoundaryName] = text(BoundaryName(_))(_.value)
  given Codec[OpName] = text(OpName(_))(_.value)
