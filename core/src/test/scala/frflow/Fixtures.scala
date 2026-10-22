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
