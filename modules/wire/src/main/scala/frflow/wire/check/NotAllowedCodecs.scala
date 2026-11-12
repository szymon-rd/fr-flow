package frflow.wire.check

import frflow.proof.reading.NotAllowed
import frflow.wire.file.Tagged
import io.circe.{Decoder, Json}

/** A rule an authored proof file broke, by its kind, with the module or word it names. */
object NotAllowedCodecs:
  def encode(n: NotAllowed): Json = n match
    case NotAllowed.Axiom           => Tagged("axiom")
    case NotAllowed.Admit           => Tagged("admit")
    case NotAllowed.Import(m)       => Tagged("import", "module" -> Json.fromString(m))
    case NotAllowed.LemmaImport(m)  => Tagged("lemma-import", "module" -> Json.fromString(m))
    case NotAllowed.Command(w)      => Tagged("command", "word" -> Json.fromString(w))

  /** A rule of the proof files of a check recorded before the prover was Rocq reads as the command it named. */
  val decoder: Decoder[NotAllowed] = Tagged.decoder("rule") {
    case "axiom"          => _ => Right(NotAllowed.Axiom)
    case "admit"          => _ => Right(NotAllowed.Admit)
    case "import"         => _.get[String]("module").map(NotAllowed.Import(_))
    case "lemma-import"   => _.get[String]("module").map(NotAllowed.LemmaImport(_))
    case "command"        => _.get[String]("word").map(NotAllowed.Command(_))
    case earlier @ ("unsafe" | "opaque" | "implemented-by" | "extern" | "native-decide" | "attribute" | "set-option" |
        "metaprogram") => _ => Right(NotAllowed.Command(earlier))
  }
