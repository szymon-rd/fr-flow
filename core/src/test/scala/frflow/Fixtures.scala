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

/** A callee reading a parameter its caller does not (the cap): the caller is proven for one cap, any cap. */
val maxPages = Param[Int]("maxPages", "the longest book the shelf may hold")
val capped = books.contract[List[Book], Int, List[Book]]("Capped", "Picking returns long books no longer than the cap.", why = "The shelf has a cap.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value && b.pages <= maxPages.value))
  .examples(minPages.bind(100), maxPages.bind(500))(
    expect(List(Book("Long", 300), Book("Huge", 900)), 5, List(Book("Long", 300)), "only the long book under the cap"),
    reject(List(Book("Huge", 900)), 5, List(Book("Huge", 900)), "never one over the cap"))
val cappedOnes = define { (shelf: List[Book], n: Int) => shelf.filter(b => b.pages >= minPages.value && b.pages <= maxPages.value) }
val cappedCall = capped.caller("cappedCall")
val viaCapped = define { (shelf: List[Book], n: Int) => cappedCall(shelf, n).filter(b => shelf.contains(b)) }
val longPick = books.contract[List[Book], Int, List[Book]]("LongPick", "Picking through Capped returns only long books from the shelf.", why = "It reuses Capped.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
// what it is decided on: these examples (a comment does not end the definition)
  .examples(minPages.bind(100), maxPages.bind(500))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))

/** A port: what an outside shelf service is trusted to return, with a cheap check of each result. */
val shelfPort = Node.port[List[Book], Int, List[Book]]("ShelfPort", "The shelf service returns long enough books from the shelf.", why = "Books come from a service.")(
  (shelf, n, r) => r.forall(b => shelf.contains(b) && b.pages >= minPages.value))
  .checkedBy((shelf, n, r) => r.forall(b => b.pages >= minPages.value))
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "the long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val fromService = define { (shelf: List[Book], n: Int) => shelf.filter(b => b.pages >= minPages.value) }

/** Code using flatMap and take: proven like a filter. */
val firstLong = define { (shelf: List[Book], n: Int) => shelf.flatMap(b => if b.pages >= minPages.value then List(b) else Nil).take(n) }

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

/** Another project's knowledge base reusing the shelf's Pick: its own root, and code calling Pick by its promise. */
val shortList = Node.root[(List[Book], Int) => List[Book]]("ShortList", "A reading list holds only books from the shelf.",
  why = "Readers choose from what is there.", safety = "A list may be empty: nothing to read is not a failure.")(
  f => forall((shelf: List[Book], n: Int) => f(shelf, n).forall(b => shelf.contains(b))))
val readingList = shortList.contract[List[Book], Int, List[Book]]("ReadingList", "A call returns only books from the shelf.", why = "ShortList, for one call.")(
  (shelf, n, r) => r.forall(b => shelf.contains(b)))
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300)), 5, List(Book("Long", 300)), "a book from the shelf"),
    expect(List(Book("Short", 20)), 5, Nil, "no book long enough"),
    reject(List(Book("Long", 300)), 5, List(Book("Other", 300)), "a book not on the shelf"))
def readerKb(shelfDir: String) = KnowledgeBase("Reader", idea = "IDEA.md")(shortList, readingList)
  .uses(shelfKb, shelfDir)(pick).implementProven(readingList)(viaPick)

/** A concern with an owner: only they decide it, and what is below it. */
val owned = Node.root[BigInt => BigInt]("Owned", "Results are never negative.", why = "Negative results are meaningless here.", owner = "ana")(
  f => forall((x: BigInt) => f(x) >= 0))
val ownedSquares = owned.refine[BigInt => BigInt]("OwnedSquares", "The result is the square of the input.", why = "Squares are never negative.")(
  abs = f => f,
  spec = f => forall((x: BigInt) => f(x) == x * x))
val ownedKb = KnowledgeBase("Owned", idea = "IDEA.md")(owned, ownedSquares)

/** Code keeping values at least a floor, whose examples do not reach the boundary (a value equal to the floor). */
val floorRoot = Node.root[(List[BigInt], BigInt) => List[BigInt]]("Floor", "No value kept is under the floor.", why = "The floor is the rule.",
  safety = "Keeping nothing is allowed: it is about what may be kept.")(
  keep => forall((xs: List[BigInt], f: BigInt) => keep(xs, f).forall(x => x >= f)))
val floorKeep = floorRoot.contract[List[BigInt], BigInt, List[BigInt]]("FloorKeep", "A call keeps no value under the floor.", why = "Floor, for one call.")(
  (xs, f, r) => r.forall(x => x >= f))
  .examples()(
    expect(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(5)), "the value over the floor"),
    expect(List(BigInt(1)), BigInt(3), Nil, "nothing over the floor"),
    reject(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1)), "a value under the floor is never kept"))
val keepAtLeast = define { (xs: List[BigInt], f: BigInt) => xs.filter(x => x >= f) }

/** Concern `i` of a team: a root its owner decides, and a refinement below it. */
def teamConcern(i: Int, owner: String): List[Node[?]] =
  val r = Node.root[BigInt => BigInt](s"NonNeg$i", "Results are never negative.", why = s"Concern $i of the team.", owner = owner)(
    f => forall((x: BigInt) => f(x) >= 0))
  List(r, r.refine[BigInt => BigInt](s"Abs$i", "The result is the absolute value of the input.", why = "It is never negative.")(
    abs = f => f, spec = f => forall((x: BigInt) => f(x) == (if x >= 0 then x else -x))))
val teamKb = KnowledgeBase("Team", idea = "IDEA.md")((0 until 5).toList.flatMap(i => teamConcern(i, s"dev$i"))*)
