package frflow.wire.snapshot

import cats.syntax.all.*
import frflow.wire.file.Tagged
import io.circe.syntax.*
import io.circe.{Codec, Decoder, Encoder}

/** What a node has beyond the rows every node has: a statement (claimed or assumed), or a design. */
enum Body:
  /** How it is checked (`Checking`, in words), the Definition it reads as a call of, the code of the Definitions it
    * mentions and their tests.
    */
  case Stated(checking: List[String], call: Option[String], code: Option[CodeRow], tested: Option[TestRow])
  case Design(governs: List[String])

object Body:
  /** By its kind, `stated` or `design`. */
  given Codec[Body] = Codec.from(
    Tagged.decoder("body") {
      case "stated" => c => (c.get[List[String]]("checking"), c.get[Option[String]]("call"),
                         c.get[Option[CodeRow]]("code"), c.get[Option[TestRow]]("tested")).mapN(Stated(_, _, _, _))
      case "design" => _.get[List[String]]("governs").map(Design(_))
    },
    Encoder.instance {
      case Stated(checking, call, code, tested) => Tagged("stated", "checking" -> checking.asJson,
                                                     "call" -> call.asJson, "code" -> code.asJson,
                                                     "tested" -> tested.asJson)
      case Design(governs)                      => Tagged("design", "governs" -> governs.asJson)
    })
