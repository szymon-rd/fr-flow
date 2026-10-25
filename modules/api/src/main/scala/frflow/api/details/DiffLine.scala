package frflow.api
package details

import io.circe.{Codec, Decoder, Encoder, Json, JsonObject}

/** In JSON `{"op": "same", "text": ...}`, `{"op": "folded", "lines": n}`: its kind a lowercase string, as other enums are. */
enum DiffLine:
  case Same(text: String)
  case Added(text: String)
  case Removed(text: String)
  case Folded(lines: Int)

object DiffLine:
  given Codec[DiffLine] = Codec.from(
    Decoder[String].at("op").flatMap {
      case "same" => Decoder[String].at("text").map(Same(_))
      case "added" => Decoder[String].at("text").map(Added(_))
      case "removed" => Decoder[String].at("text").map(Removed(_))
      case "folded" => Decoder[Int].at("lines").map(Folded(_))
      case other => Decoder.failedWithMessage(s"no diff line op $other")
    },
    Encoder.AsObject.instance {
      case Same(t) => JsonObject("op" -> Json.fromString("same"), "text" -> Json.fromString(t))
      case Added(t) => JsonObject("op" -> Json.fromString("added"), "text" -> Json.fromString(t))
      case Removed(t) => JsonObject("op" -> Json.fromString("removed"), "text" -> Json.fromString(t))
      case Folded(n) => JsonObject("op" -> Json.fromString("folded"), "lines" -> Json.fromInt(n))
    })
