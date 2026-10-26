package frflow.protocol

/** How a Scala name is written as a word: `ModelError` as `model-error`. */
object Spelling:
  def word(name: String): String = name.replaceAll("([a-z])([A-Z])", "$1-$2").toLowerCase
