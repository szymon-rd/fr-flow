package frflow.protocol

/** Whether what the developer wrote says something (re-exported by `frflow.protocol`). */
object Prose:
  /** A reason, a why or an exemption says something: a few words, not a placeholder. */
  def tooFew(s: String): Boolean = s.trim.split("\\s+").count(_.exists(_.isLetter)) < 3
