package frflow.fixtures

import frflow.*

/** A small shelf: a root over generic items, definitions that introduce books, three parts in their
  * terms, and a contract on the shelf service's operation under all three.
  */
val Item = Opaque("Item", "a thing that can be picked")
val good = Param[Item.T => Boolean]("good", "whether an item is worth picking")
val shown = Param[(List[Item.T], Item.T) => Boolean]("shown", "whether the item is picked when the list is offered")

val onlyGood = Node.claim("OnlyGood", "An item is picked from a list exactly when it is on the list and good.",
  why = "Picking a bad item is what the idea rules out; leaving a good one is what it asks not to.")(
  forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good(x))))

final case class Book(title: String, pages: Int)
enum Shelf:
  case Top, Bottom
  case Box(label: String)

val minPages = Param[Int]("minPages", "the length readers asked for, from the settings")
val picks = Param[(List[Book], Int) => List[Book]]("picks", "the books the shelf service picks from a shelf, asked for n")

val books = Node.definition("Books", "Items are books; a book is good when it is long enough.", why = "The shelf holds books, and length is what readers asked for.")(
  Item := of[Book],
  good := ((b: Book) => b.pages >= minPages.value))
val picking = Node.definition("Picking", "A book is picked from a shelf when the service picks it, asked for as many as the shelf holds.",
  why = "The service is how books leave the shelf.")(
  shown := ((l: List[Book], b: Book) => picks(l, l.length).contains(b)))

val fromList = Node.claim("FromList", "Picked books come from the shelf.", why = "Nothing else can be handed out.")(
  forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood)
val onlyLong = Node.claim("OnlyLong", "Picked books are long enough.", why = "A short book is not worth picking.")(
  forall((l: List[Book], n: Int) => picks(l, n).forall(b => b.pages >= minPages.value))).under(onlyGood)
val everyLong = Node.claim("EveryLong", "Every long enough book on the shelf is picked.", why = "Readers want every good book.")(
  forall((l: List[Book], n: Int) => l.forall(b => b.pages >= minPages.value ==> picks(l, n).contains(b)))).under(onlyGood)
val shelfParts = Seq(fromList, onlyLong, everyLong)

val pick = Node.contract(picks)("Pick", "A call returns exactly the long enough books of the shelf.", why = "The three parts, for one call, checked on every result.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value) && shelf.forall(b => b.pages >= minPages.value ==> picked.contains(b)))
  .under(fromList, onlyLong, everyLong)
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    expect(List(Book("Short", 20)), 5, Nil, "no book is long enough: none is picked"),
    reject(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Short", 20)), "a short book is never picked"),
    reject(List(Book("Long", 300)), 5, Nil, "a long book is not left on the shelf"))

def shelfNodes: List[Node[?]] = List(onlyGood, books, picking, fromList, onlyLong, everyLong)
val shelfKb = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick)*)
  .implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value))

/** The shelf with another contract in Pick's place. */
def shelfWith(c: Node[?], more: Node[?]*): KnowledgeBase = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes ++ (c +: more))*)

/** Defined functions. */
val long = define { (b: Book) => b.pages >= 100 }
val where = define { (s: Shelf) =>
  s match
    case Shelf.Top    => "top"
    case Shelf.Bottom => "bottom"
    case Shelf.Box(l) => l
}

/** A part that does not make its parent: picking few items says nothing about goodness. */
val sloppy = Node.claim("Sloppy", "At most n books are picked.", why = "A bound on the number of books.")(
  forall((l: List[Book], n: Int) => picks(l, n).length <= n)).under(onlyGood)
val sloppyKb = KnowledgeBase("Sloppy", idea = "IDEA.md")(onlyGood, books, picking, sloppy)

/** A split `frflow_auto` does not prove (nonlinear arithmetic): it needs an authored proof. */
val sq = Param[BigInt => BigInt]("sq", "what the calculator returns for a number")
val nonNegative = Node.claim("NonNegative", "Results are never negative.", why = "Negative results are meaningless here.")(
  forall((x: BigInt) => sq(x) >= 0))
val squares = Node.claim("Squares", "The result is the square of the input.", why = "Squares are never negative.")(
  forall((x: BigInt) => sq(x) == x * x)).under(nonNegative)
val squareKb = KnowledgeBase("Square", idea = "IDEA.md")(nonNegative, squares)

/** Implementations written as definitions, for proven implementations. */
val longOnes = define { (shelf: List[Book], n: Int) => shelf.filter(b => b.pages >= minPages.value) }
val anyOnes = define { (shelf: List[Book], n: Int) => shelf }

/** A filter, hidden in a definition. */
val onShelf = define { (shelf: List[Book], picked: List[Book]) => picked.filter(b => shelf.contains(b)) }

/** Pick, renamed: the same contract under another name. */
val choose = Node.contract(picks)("Choose", "A call returns exactly the long enough books of the shelf.", why = "The three parts, for one call, checked on every result.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value) && shelf.forall(b => b.pages >= minPages.value ==> picked.contains(b)))
  .under(fromList, onlyLong, everyLong)
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    expect(List(Book("Short", 20)), 5, Nil, "no book is long enough: none is picked"),
    reject(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Short", 20)), "a short book is never picked"),
    reject(List(Book("Long", 300)), 5, Nil, "a long book is not left on the shelf"))

/** Code that calls another contract's operation, proven from that contract's promise, not its code. */
val again = Param[(List[Book], Int) => List[Book]]("again", "the books picked again, through the shelf service")
val pickedAgain = Node.claim("PickedAgain", "Books picked again come from the shelf and are long enough.", why = "Picking again is picking.")(
  forall((l: List[Book], n: Int) => again(l, n).forall(b => l.contains(b) && b.pages >= minPages.value)))
val pickPromise = Node.contract(picks)("PickPromise", "A call returns only long enough books from the shelf.", why = "What code calling the service relies on.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value))
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val viaPick = define { (shelf: List[Book], n: Int) => picks(shelf, n).filter(b => shelf.contains(b)) }
val againC = Node.contract(again)("Again", "Picking again, through the service, returns only long books from the shelf.", why = "It reuses the service.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(pickedAgain)
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val callsKb = KnowledgeBase("Calls", idea = "IDEA.md")(pickedAgain, againC, pickPromise)
  .implementProven(pickPromise)(longOnes).implementProven(againC)(viaPick)

/** A callee reading a parameter its caller does not (the cap): the caller is proven for one cap, any cap. */
val maxPages = Param[Int]("maxPages", "the longest book the shelf may hold")
val cappedOp = Param[(List[Book], Int) => List[Book]]("cappedOp", "the books the capped shelf service picks")
val capped = Node.contract(cappedOp)("Capped", "Picking returns long books no longer than the cap.", why = "The shelf has a cap.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value && b.pages <= maxPages.value))
  .examples(minPages.bind(100), maxPages.bind(500))(
    expect(List(Book("Long", 300), Book("Huge", 900)), 5, List(Book("Long", 300)), "only the long book under the cap"),
    expect(List(Book("Short", 20)), 5, Nil, "no long book"),
    reject(List(Book("Huge", 900)), 5, List(Book("Huge", 900)), "never one over the cap"))
val cappedOnes = define { (shelf: List[Book], n: Int) => shelf.filter(b => b.pages >= minPages.value && b.pages <= maxPages.value) }
val viaCapped = define { (shelf: List[Book], n: Int) => cappedOp(shelf, n).filter(b => shelf.contains(b)) }
val longPicked = Param[(List[Book], Int) => List[Book]]("longPicked", "the long books picked through the capped service")
val pickedLong = Node.claim("PickedLong", "Books picked through the capped service come from the shelf and are long enough.", why = "Readers want long books.")(
  forall((l: List[Book], n: Int) => longPicked(l, n).forall(b => l.contains(b) && b.pages >= minPages.value)))
val longPick = Node.contract(longPicked)("LongPick", "Picking through Capped returns only long books from the shelf.", why = "It reuses Capped.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(pickedLong)
// what it is decided on: these examples (a comment does not end the definition)
  .examples(minPages.bind(100), maxPages.bind(500))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    expect(List(Book("Short", 20)), 5, Nil, "no long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))

/** An assumption on an operation: what an outside shelf service is trusted to return, with a cheap
  * check of each result; Pick's code calls it.
  */
val fetch = Param[(List[Book], Int) => List[Book]]("fetch", "what the outside shelf service returns for a shelf")
val shelfPort = Node.assumption(fetch)("ShelfPort", "The shelf service returns exactly the long enough books of the shelf.", why = "Books come from a service.")(
  (shelf, n, r) => r.forall(b => shelf.contains(b) && b.pages >= minPages.value) && shelf.forall(b => b.pages >= minPages.value ==> r.contains(b)))
  .checkedBy((shelf, n, r) => r.forall(b => b.pages >= minPages.value))
  .examples(minPages.bind(100))(
    expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "the long book"),
    reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val fromService = define { (shelf: List[Book], n: Int) => shelf.filter(b => b.pages >= minPages.value) }
val viaFetch = define { (shelf: List[Book], n: Int) => fetch(shelf, n).filter(b => shelf.contains(b)) }

/** Code using flatMap: proven like a filter. */
val firstLong = define { (shelf: List[Book], n: Int) => shelf.flatMap(b => if b.pages >= minPages.value then List(b) else Nil) }

/** State kept in a map: counts by name, each bump adding one to its own count only. */
val bumps = Param[(Map[String, BigInt], String) => Map[String, BigInt]]("bumps", "the counts after a bump of a name")
val counts = Node.claim("Counts", "A bump adds one to its name's count, and leaves the others.", why = "Counting.")(
  forall((m: Map[String, BigInt], k: String) => bumps(m, k).get(k) == Some(m.getOrElse(k, BigInt(0)) + 1)) &&
    forall((m: Map[String, BigInt], k: String) => forall((j: String) => j == k || bumps(m, k).get(j) == m.get(j))))
val bump = Node.contract(bumps)("Bump", "A bump adds one to its name's count, and leaves the others.", why = "Per call.")(
  (m, k, r) => r.get(k) == Some(m.getOrElse(k, BigInt(0)) + 1) && r.removed(k) == m.removed(k)).under(counts)
  .examples()(
    expect(Map("a" -> BigInt(1)), "a", Map("a" -> BigInt(2)), "a counted twice"),
    expect(Map("a" -> BigInt(1)), "b", Map("a" -> BigInt(1), "b" -> BigInt(1)), "b counted once, a left"),
    reject(Map("a" -> BigInt(1)), "b", Map("b" -> BigInt(1)), "a lost"))
val bumped = define { (m: Map[String, BigInt], k: String) => m.updated(k, m.getOrElse(k, BigInt(0)) + 1) }

/** Code keeping values at least a floor, whose examples do not reach the boundary (a value equal to the floor). */
val retained = Param[(List[BigInt], BigInt) => List[BigInt]]("retained", "the values kept from a list, given the floor")
val floorRoot = Node.claim("Floor", "A value is kept exactly when it is on the list and not under the floor.", why = "The floor is the rule.")(
  forall((xs: List[BigInt], f: BigInt) => retained(xs, f).forall(x => xs.contains(x) && x >= f) && xs.forall(x => x >= f ==> retained(xs, f).contains(x))))
val floorKeep = Node.contract(retained)("FloorKeep", "A call keeps exactly the values of the list not under the floor.", why = "Floor, for one call.")(
  (xs, f, r) => r.forall(x => xs.contains(x) && x >= f) && xs.forall(x => x >= f ==> r.contains(x))).under(floorRoot)
  .examples()(
    expect(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(5)), "the value over the floor"),
    expect(List(BigInt(1)), BigInt(3), Nil, "nothing over the floor"),
    reject(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1)), "a value under the floor is never kept"))
val keepAtLeast = define { (xs: List[BigInt], f: BigInt) => xs.filter(x => x >= f) }

/** Defined functions of four and five arguments, called like the others. */
val pagesBetween = define { (b: Book, lo: Int, hi: Int, title: String) => b.pages >= lo && b.pages <= hi && b.title != title }
val pagesBetweenOn = define { (b: Book, lo: Int, hi: Int, title: String, s: Shelf) => pagesBetween(b, lo, hi, title) && where(s) != title }

/** Code reading a defined term whose definition calls the shelf service: it does not call the service
  * itself, so the service's promise is no hypothesis of its proof.
  */
val pickedFrom = Param[(List[Book], Book) => Boolean]("pickedFrom", "whether the shelf service picks the book from the shelf")
val pickedFromDef = Node.definition("PickedFrom", "A book is picked from a shelf when the service picks it, asked for the whole shelf.",
  why = "The service is how books leave the shelf.")(pickedFrom := ((l: List[Book], b: Book) => picks(l, l.length).contains(b)))
val viaPickedFrom = define { (shelf: List[Book], n: Int) => shelf.filter(b => pickedFrom(shelf, b) && b.pages >= minPages.value) }
val readsKb = KnowledgeBase("Reads", idea = "IDEA.md")(pickedAgain, againC, pickPromise, pickedFromDef)
  .implementProven(pickPromise)(longOnes).implementProven(againC)(viaPickedFrom)

/** Membership through a set built once (`toSet`): a hash set in Scala, the list's membership in Lean. */
val kept = Param[(List[Book], List[Book]) => List[Book]]("kept", "the picked books a check keeps, those on the shelf")
val keptOnShelf = Node.claim("KeptOnShelf", "A book is kept exactly when it was picked and is on the shelf.", why = "Only books of the shelf leave it.")(
  forall((s: List[Book], p: List[Book]) => forall((b: Book) => kept(s, p).contains(b) == (p.contains(b) && s.contains(b)))))
val keep = Node.contract(kept)("Keep", "A call keeps exactly the picked books that are on the shelf.", why = "KeptOnShelf, for one call.")(
  (s, p, r) => r.forall(b => p.contains(b) && s.toSet.contains(b)) && p.forall(b => s.toSet.contains(b) ==> r.contains(b))).under(keptOnShelf)
  .examples()(
    expect(List(Book("A", 100)), List(Book("A", 100), Book("B", 200)), List(Book("A", 100)), "the book on the shelf"),
    reject(List(Book("A", 100)), List(Book("B", 200)), List(Book("B", 200)), "never a book off the shelf"),
    reject(List(Book("A", 100)), List(Book("A", 100)), Nil, "never drops a book on the shelf"))
val keptOnce = define { (shelf: List[Book], picked: List[Book]) =>
  val there = shelf.toSet
  picked.filter(b => there.contains(b))
}
val keepKb = KnowledgeBase("Keep", idea = "IDEA.md")(keptOnShelf, keep).implementProven(keep)(keptOnce)
