package frflow.wire.check

import frflow.proof.reading.NotAllowed
import frflow.wire.file.Tagged
import io.circe.{Decoder, Json}

/** A rule an authored proof file broke, by its kind, with the option, command, module or word it names. */
object NotAllowedCodecs:
  def encode(n: NotAllowed): Json = n match
    case NotAllowed.Axiom           => Tagged("axiom")
    case NotAllowed.Admit           => Tagged("admit")
    case NotAllowed.Unsafe          => Tagged("unsafe")
    case NotAllowed.Opaque          => Tagged("opaque")
    case NotAllowed.ImplementedBy   => Tagged("implemented-by")
    case NotAllowed.Extern          => Tagged("extern")
    case NotAllowed.NativeDecide    => Tagged("native-decide")
    case NotAllowed.Attribute       => Tagged("attribute")
    case NotAllowed.SetOption(o)    => Tagged("set-option", "option" -> Json.fromString(o))
    case NotAllowed.Metaprogram(c)  => Tagged("metaprogram", "command" -> Json.fromString(c))
    case NotAllowed.Import(m)       => Tagged("import", "module" -> Json.fromString(m))
    case NotAllowed.LemmaImport(m)  => Tagged("lemma-import", "module" -> Json.fromString(m))
    case NotAllowed.Command(w)      => Tagged("command", "word" -> Json.fromString(w))

  val decoder: Decoder[NotAllowed] = Tagged.decoder("rule") {
    case "axiom"          => _ => Right(NotAllowed.Axiom)
    case "admit"          => _ => Right(NotAllowed.Admit)
    case "unsafe"         => _ => Right(NotAllowed.Unsafe)
    case "opaque"         => _ => Right(NotAllowed.Opaque)
    case "implemented-by" => _ => Right(NotAllowed.ImplementedBy)
    case "extern"         => _ => Right(NotAllowed.Extern)
    case "native-decide"  => _ => Right(NotAllowed.NativeDecide)
    case "attribute"      => _ => Right(NotAllowed.Attribute)
    case "set-option"     => _.get[String]("option").map(NotAllowed.SetOption(_))
    case "metaprogram"    => _.get[String]("command").map(NotAllowed.Metaprogram(_))
    case "import"         => _.get[String]("module").map(NotAllowed.Import(_))
    case "lemma-import"   => _.get[String]("module").map(NotAllowed.LemmaImport(_))
    case "command"        => _.get[String]("word").map(NotAllowed.Command(_))
  }
