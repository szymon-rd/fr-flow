package frflow.fixtures

import frflow.*

/** A small generic knowledge base: an opaque item with a parameter, refined, instantiated, contracted. */
val Item = Opaque("Item")
val good = Param[Item.T => Boolean]("good")

/** Model: picking up to `n` items from a list. */
val onlyGood = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", "Only good items are picked.")(
  pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))

val listed = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Picked items come from the list and are good.")(
  abs = pick => pick,
  spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))

final case class Book(title: String, pages: Int)
enum Shelf:
  case Top, Bottom
  case Box(label: String)

val minPages = Param[Int]("minPages")

val books = listed.instantiate[(List[Book], Int) => List[Book]]("Books", "Items are books; a book is good when it is long enough.")(
  Item := of[Book],
  good := ((b: Book) => b.pages >= minPages.value))

val pick = books.contract[List[Book], Int, List[Book]]("Pick", "Picking returns only long enough books.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))

val shelfKb = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick)

/** Defined functions. */
val long = define { (b: Book) => b.pages >= 100 }
val where = define { (s: Shelf) =>
  s match
    case Shelf.Top    => "top"
    case Shelf.Bottom => "bottom"
    case Shelf.Box(l) => l
}

/** A refinement that does not imply its parent: picking few items says nothing about goodness. */
val sloppy = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Sloppy", "At most n items are picked.")(
  abs = pick => pick,
  spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).length <= n))

val sloppyKb = KnowledgeBase("Sloppy", idea = "IDEA.md")(onlyGood, sloppy)

/** A link `frflow_auto` does not prove (nonlinear arithmetic): it needs an authored proof. */
val nonNegative = Node.root[Int => Int]("NonNegative", "Results are never negative.")(f => forall((x: Int) => f(x) >= 0))
val squares = nonNegative.refine[Int => Int]("Squares", "The result is the square of the input.")(
  abs = f => f,
  spec = f => forall((x: Int) => f(x) == x * x))

val squareKb = KnowledgeBase("Square", idea = "IDEA.md")(nonNegative, squares)
