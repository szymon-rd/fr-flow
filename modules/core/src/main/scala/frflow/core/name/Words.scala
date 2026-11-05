package frflow.core.name

/** The rule on the developer's own words where a reason is asked for (a decision's, an exemption's): at least three
  * words (today's `tooFew`).
  */
object Words:
  def enough(text: String): Boolean = text.trim.split("\\s+").count(_.exists(_.isLetter)) >= 3
