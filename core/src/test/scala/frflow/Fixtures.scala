package frflow.fixtures

import frflow.*

/** A small generic knowledge base: an opaque item with a parameter, refined, instantiated, contracted. */
val Item = Opaque("Item", "a thing that can be picked")
val good = Param[Item.T => Boolean]("good", "whether an item is worth picking")

/** Model: picking up to `n` items from a list. */
val onlyGood = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", "Only good items are picked.", why = "Picking a bad item is the failure the idea rules out.")(
  pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))

val listed = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Picked items come from the list and are good.", why = "Items can only come from the list offered; abs is the identity.")(
  abs = pick => pick,
  spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))

final case class Book(title: String, pages: Int)
enum Shelf:
  case Top, Bottom
  case Box(label: String)

val minPages = Param[Int]("minPages", "the length readers asked for, from the settings")

val books = listed.instantiate[(List[Book], Int) => List[Book]]("Books", "Items are books; a book is good when it is long enough.", why = "The shelf holds books, and length is what readers asked for.")(
  Item := of[Book],
  good := ((b: Book) => b.pages >= minPages.value))

val pick = books.contract[List[Book], Int, List[Book]]("Pick", "Picking returns only long enough books.", why = "The per-call form of Books, checked on every result.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    expect(List(Book("Short", 20)), 5, Nil, "no book is long enough: none is picked"),
    reject(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Short", 20)), "a short book is never picked"))

val shelfKb = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick)
  .implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value).take(n))

/** Defined functions. */
val long = define { (b: Book) => b.pages >= 100 }
val where = define { (s: Shelf) =>
  s match
    case Shelf.Top    => "top"
    case Shelf.Bottom => "bottom"
    case Shelf.Box(l) => l
}

/** A refinement that does not imply its parent: picking few items says nothing about goodness. */
val sloppy = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Sloppy", "At most n items are picked.", why = "A bound on the number of items.")(
  abs = pick => pick,
  spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).length <= n))

val sloppyKb = KnowledgeBase("Sloppy", idea = "IDEA.md")(onlyGood, sloppy)

/** A link `frflow_auto` does not prove (nonlinear arithmetic): it needs an authored proof. */
val nonNegative = Node.root[BigInt => BigInt]("NonNegative", "Results are never negative.", why = "Negative results are meaningless here.")(f => forall((x: BigInt) => f(x) >= 0))
val squares = nonNegative.refine[BigInt => BigInt]("Squares", "The result is the square of the input.", why = "Squares are never negative.")(
  abs = f => f,
  spec = f => forall((x: BigInt) => f(x) == x * x))

val squareKb = KnowledgeBase("Square", idea = "IDEA.md")(nonNegative, squares)

/** Implementations written as definitions, for proven implementations. */
val longOnes = define { (shelf: List[Book], n: Int) => shelf.filter(b => b.pages >= minPages.value) }
val anyOnes = define { (shelf: List[Book], n: Int) => shelf }

/** A filter, hidden in a definition. */
val onShelf = define { (shelf: List[Book], picked: List[Book]) => picked.filter(b => shelf.contains(b)) }

/** Pick, renamed: the same contract under another name. */
val choose = books.contract[List[Book], Int, List[Book]]("Choose", "Picking returns only long enough books.", why = "The per-call form of Books, checked on every result.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    expect(List(Book("Short", 20)), 5, Nil, "no book is long enough: none is picked"),
    reject(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Short", 20)), "a short book is never picked"))

/** Code that calls another contract (Pick) by its promise, not by its code. */
val pickCall = pick.caller("pickCall")
val viaPick = define { (shelf: List[Book], n: Int) => pickCall(shelf, n).filter(b => shelf.contains(b)) }
val again = books.contract[List[Book], Int, List[Book]]("Again", "Picking again, through Pick, returns only long books from the shelf.", why = "It reuses Pick.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
  .examples(minPages.bind(100), pickCall.bind((s: List[Book], k: Int) => s.filter(b => b.pages >= minPages.value)))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))

/** State kept in a map: counts by name, each bump adding one to its own count only. */
val counts = Node.root[(Map[String, BigInt], String) => Map[String, BigInt]]("Counts", "A bump adds one to its name's count, and leaves the others.", why = "Counting.")(
  f => forall((m: Map[String, BigInt], k: String) => f(m, k).get(k) == Some(m.getOrElse(k, BigInt(0)) + 1)) &&
    forall((m: Map[String, BigInt], k: String) => forall((j: String) => j == k || f(m, k).get(j) == m.get(j))))
val bump = counts.contract[Map[String, BigInt], String, Map[String, BigInt]]("Bump", "A bump adds one to its name's count, and leaves the others.", why = "Per call.")(
  (m, k, r) => r.get(k) == Some(m.getOrElse(k, BigInt(0)) + 1) && r.removed(k) == m.removed(k))
  .examples()(
    expect(Map("a" -> BigInt(1)), "a", Map("a" -> BigInt(2)), "a counted twice"),
    expect(Map("a" -> BigInt(1)), "b", Map("a" -> BigInt(1), "b" -> BigInt(1)), "b counted once, a left"),
    reject(Map("a" -> BigInt(1)), "b", Map("b" -> BigInt(1)), "a lost"))
val bumped = define { (m: Map[String, BigInt], k: String) => m.updated(k, m.getOrElse(k, BigInt(0)) + 1) }
