package frflow.testing

import frflow.*

/** Today's testing fixture in the three kinds: a shelf service picking the long enough books, its threshold provided
  * where the code runs, and arities zero to three for the generated tests (`TestingSuite`).
  */
object Shelf:
  final case class Book(title: String, pages: BigInt) derives LeanType

  enum Place derives LeanType:
    case Top, Bottom
    case Box(label: String, books: List[Book])

  val minPages = Definition[BigInt]("the length readers asked for, from the settings")
  val picks = Definition[(List[Book], BigInt) => List[Book]](
    "the books the shelf service picks from a shelf, asked for n")

  val pick = Node.claim("A call returns exactly the long enough books of the shelf.")(
    forall((shelf: Term[List[Book]], n: Term[BigInt]) =>
      picks(shelf, n).forall(b => shelf.contains(b) && b.pages >= minPages) &&
        shelf.forall(b => b.pages >= minPages implies picks(shelf, n).contains(b))))

  /** The shelf with `code` as the picking service's. */
  def withCode(code: BigInt => (List[Book], BigInt) => List[Book]): FrModel =
    FrModel("Shelf")(pick).implementProvided(minPages)
      .implementTested(picks)(env => code(env(minPages)))

  val kb: FrModel = withCode(min => (shelf, _) => shelf.filter(_.pages >= min))

  // One input: the longest book's pages.
  val longest = Definition[List[Book] => BigInt]("the most pages of a book on the shelf, 0 for none")
  val noLonger = Node.claim("No book on the shelf is longer than the longest.")(
    forall((shelf: Term[List[Book]]) => shelf.forall(b => b.pages <= longest(shelf))))

  // Three inputs: the books between two lengths.
  val between = Definition[(List[Book], BigInt, BigInt) => List[Book]]("the books picked between two lengths")
  val inRange = Node.claim("Books picked between two lengths come from the shelf and are between them.")(
    forall((shelf: Term[List[Book]], lo: Term[BigInt], hi: Term[BigInt]) =>
      between(shelf, lo, hi).forall(b => shelf.contains(b) && lo <= b.pages && b.pages <= hi)))

  // No input: what the shelf holds today, against its rule.
  val today = Definition[List[Book]]("the books on the shelf today")
  val todayLong = Node.claim("Every book on the shelf today has at least the length asked for.")(
    today.forall(b => b.pages >= minPages))
