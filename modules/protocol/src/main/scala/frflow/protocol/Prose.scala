package frflow.protocol

/** Whether what the developer wrote says something. */
object Prose:
  /** A reason, a why or an exemption of fewer than three words says nothing. */
  def tooFew(s: String): Boolean = s.trim.split("\\s+").count(_.exists(_.isLetter)) < 3
