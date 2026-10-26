package frflow.decision.content

/** Contents of two forms compared on what both have. The form is read off the content, which a signature covers. */
object Formats:
  val retired: Set[String] = Set("definition", "idea", "ideaSection", "notModelled")
  val added: Set[String] = Set("reliance", "failure")

  /** `V1` contents always have `definition` (today's `Contents.of` writes it for every kind; the four examples'
    * ledgers are checked in step 0); the retired `IDEA` contents are never compared.
    */
  def of(c: Content): Format = if c.get("definition").isDefined then Format.V1 else Format.V2

  /** A decided content and the content now, each without the fields the decided one's form lacks. */
  def aligned(decided: Content, now: Content): (Content, Content) = of(decided) match
    case Format.V1 => (decided.without(retired), now.without(k => retired(k) || added(k)))
    case Format.V2 => (decided, now)
