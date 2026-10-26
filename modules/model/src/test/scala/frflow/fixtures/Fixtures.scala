package frflow.fixtures

import frflow.*

/** A small shelf: a root over generic items, definitions that introduce books, three parts in their
  * terms, and a contract on the shelf service's operation under all three.
  */
val Item = Opaque("Item", "a thing that can be picked")
val good = Param[Item.T => Boolean]("whether an item is worth picking")
val shown = Param[(List[Item.T], Item.T) => Boolean]("whether the item is picked when the list is offered")

val onlyGood = Node.claim("An item is picked from a list exactly when it is on the list and good.",
  why = "Picking a bad item is what the idea rules out; leaving a good one is what it asks not to.")(
  forall((l: Term[List[Item.T]], x: Term[Item.T]) => shown(l, x) === (l.contains(x) && good(x))))

val minPages = Param[Int]("the length readers asked for, from the settings")
val picks = Param[(List[Book], Int) => List[Book]]("the books the shelf service picks from a shelf, asked for n")

val books = Node.definition("Items are books; a book is good when it is long enough.", why = "The shelf holds books, and length is what readers asked for.")(
  Item := of[Book],
  good := ((b: Term[Book]) => b.pages >= minPages))
val picking = Node.definition("A book is picked from a shelf when the service picks it, asked for as many as the shelf holds.",
  why = "The service is how books leave the shelf.")(
  shown := ((l: Term[List[Book]], b: Term[Book]) => picks(l, l.length).contains(b)))

val fromList = Node.claim("Picked books come from the shelf.", why = "Nothing else can be handed out.")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b)))).refines(onlyGood)
val onlyLong = Node.claim("Picked books are long enough.", why = "A short book is not worth picking.")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => b.pages >= minPages))).refines(onlyGood)
val everyLong = Node.claim("Every long enough book on the shelf is picked.", why = "Readers want every good book.")(
  forall((l: Term[List[Book]], n: Term[Int]) => l.forall(b => b.pages >= minPages implies picks(l, n).contains(b)))).refines(onlyGood)
val shelfParts = Seq(fromList, onlyLong, everyLong)

val pick = Node.contract(picks)("A call returns exactly the long enough books of the shelf.", why = "The three parts, for one call, checked on every result.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages) && shelf.forall(b => b.pages >= minPages implies picked.contains(b)))
  .refines(fromList, onlyLong, everyLong)
  .examples(minPages.bind(100))(
    allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    allows(List(Book("Short", 20)), 5, Nil, "no book is long enough: none is picked"),
    forbids(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Short", 20)), "a short book is never picked"),
    forbids(List(Book("Long", 300)), 5, Nil, "a long book is not left on the shelf"))

def shelfNodes: List[Node[?]] = List(onlyGood, books, picking, fromList, onlyLong, everyLong)
val shelfKb = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes :+ pick)*)
  .implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value))

/** The shelf with another contract in Pick's place. */
def shelfWith(c: Node[?], more: Node[?]*): KnowledgeBase = KnowledgeBase("Shelf", idea = "IDEA.md")((shelfNodes ++ (c +: more))*)

/** Defined functions. */
val long = define { (b: Term[Book]) => b.pages >= 100 }
val otherTitles = define { (a: Term[Book], b: Term[Book]) => a.title =!= b.title }
val where = define { (s: Term[Shelf]) =>
  s.on[Shelf.Top.type]("top")
    .on[Shelf.Bottom.type]("bottom")
    .on[Shelf.Box](l => l)
}

/** A part that does not make its parent: picking few items says nothing about goodness. */
val sloppy = Node.claim("At most n books are picked.", why = "A bound on the number of books.")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).length <= n)).refines(onlyGood)
val sloppyKb = KnowledgeBase("Sloppy", idea = "IDEA.md")(onlyGood, books, picking, sloppy)

/** A split `frflow_auto` does not prove (nonlinear arithmetic): it needs an authored proof. */
val sq = Param[BigInt => BigInt]("what the calculator returns for a number")
val nonNegative = Node.claim("Results are never negative.", why = "Negative results are meaningless here.")(
  forall((x: Term[BigInt]) => sq(x) >= 0))
val squares = Node.claim("The result is the square of the input.", why = "Squares are never negative.")(
  forall((x: Term[BigInt]) => sq(x) === x * x)).refines(nonNegative)
val squareKb = KnowledgeBase("Square", idea = "IDEA.md")(nonNegative, squares)

/** Implementations written as definitions, for proven implementations. */
val longOnes = define { (shelf: Term[List[Book]], n: Term[Int]) => shelf.filter(b => b.pages >= minPages) }
val anyOnes = define { (shelf: Term[List[Book]], n: Term[Int]) => shelf }

/** A filter, hidden in a definition. */
val onShelf = define { (shelf: Term[List[Book]], picked: Term[List[Book]]) => picked.filter(b => shelf.contains(b)) }

/** Code that calls another contract's operation, proven from that contract's promise, not its code. */
val again = Param[(List[Book], Int) => List[Book]]("the books picked again, through the shelf service")
val pickedAgain = Node.claim("Books picked again come from the shelf and are long enough.", why = "Picking again is picking.")(
  forall((l: Term[List[Book]], n: Term[Int]) => again(l, n).forall(b => l.contains(b) && b.pages >= minPages)))
val pickPromise = Node.contract(picks)("A call returns only long enough books from the shelf.", why = "What code calling the service relies on.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages))
  .examples(minPages.bind(100))(
    allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    forbids(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val viaPick = define { (shelf: Term[List[Book]], n: Term[Int]) => picks(shelf, n).filter(b => shelf.contains(b)) }
/** The contract on `again`, in an object of its own: named `again` too, it would hide the operation. */
object Again:
  val again = Node.contract(fixtures.again)("Picking again, through the service, returns only long books from the shelf.",
    why = "It reuses the service.")(
    (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages)).refines(pickedAgain)
    .examples(minPages.bind(100))(
      allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
      forbids(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val callsKb = KnowledgeBase("Calls", idea = "IDEA.md")(pickedAgain, Again.again, pickPromise)
  .implementProven(pickPromise)(longOnes).implementProven(Again.again)(viaPick)

/** A callee reading a parameter its caller does not (the cap): the caller is proven for one cap, any cap. */
val maxPages = Param[Int]("the longest book the shelf may hold")
val cappedOp = Param[(List[Book], Int) => List[Book]]("the books the capped shelf service picks")
val capped = Node.contract(cappedOp)("Picking returns long books no longer than the cap.", why = "The shelf has a cap.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages && b.pages <= maxPages))
  .examples(minPages.bind(100), maxPages.bind(500))(
    allows(List(Book("Long", 300), Book("Huge", 900)), 5, List(Book("Long", 300)), "only the long book under the cap"),
    allows(List(Book("Short", 20)), 5, Nil, "no long book"),
    forbids(List(Book("Huge", 900)), 5, List(Book("Huge", 900)), "never one over the cap"))
val cappedOnes = define { (shelf: Term[List[Book]], n: Term[Int]) => shelf.filter(b => b.pages >= minPages && b.pages <= maxPages) }
val viaCapped = define { (shelf: Term[List[Book]], n: Term[Int]) => cappedOp(shelf, n).filter(b => shelf.contains(b)) }
val longPicked = Param[(List[Book], Int) => List[Book]]("the long books picked through the capped service")
val pickedLong = Node.claim("Books picked through the capped service come from the shelf and are long enough.", why = "Readers want long books.")(
  forall((l: Term[List[Book]], n: Term[Int]) => longPicked(l, n).forall(b => l.contains(b) && b.pages >= minPages)))
val longPick = Node.contract(longPicked)("Picking through Capped returns only long books from the shelf.", why = "It reuses Capped.")(
  (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages)).refines(pickedLong)
// what it is decided on: these examples (a comment does not end the definition)
  .examples(minPages.bind(100), maxPages.bind(500))(
    allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
    allows(List(Book("Short", 20)), 5, Nil, "no long book"),
    forbids(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))

/** An assumption on an operation: what an outside shelf service is trusted to return, with a cheap
  * check of each result; Pick's code calls it.
  */
val fetch = Param[(List[Book], Int) => List[Book]]("what the outside shelf service returns for a shelf")
val shelfPort = Node.assumption(fetch)("The shelf service returns exactly the long enough books of the shelf.", why = "Books come from a service.")(
  (shelf, n, r) => r.forall(b => shelf.contains(b) && b.pages >= minPages) && shelf.forall(b => b.pages >= minPages implies r.contains(b)))
  .checkedBy((shelf, n, r) => r.forall(b => b.pages >= minPages))
  .examples(minPages.bind(100))(
    allows(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "the long book"),
    forbids(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
val fromService = define { (shelf: Term[List[Book]], n: Term[Int]) => shelf.filter(b => b.pages >= minPages) }
val viaFetch = define { (shelf: Term[List[Book]], n: Term[Int]) => fetch(shelf, n).filter(b => shelf.contains(b)) }

/** Code using flatMap: proven like a filter. */
val firstLong = define { (shelf: Term[List[Book]], n: Term[Int]) => shelf.flatMap(b => (b.pages >= minPages).fold(List(b), Nil)) }

/** State kept in a map: counts by name, each bump adding one to its own count only. */
val bumps = Param[(Map[String, BigInt], String) => Map[String, BigInt]]("the counts after a bump of a name")
val counts = Node.claim("A bump adds one to its name's count, and leaves the others.", why = "Counting.")(
  forall((m: Term[Map[String, BigInt]], k: Term[String]) => bumps(m, k).get(k) === Some(m.getOrElse(k, BigInt(0)) + 1)) &&
    forall((m: Term[Map[String, BigInt]], k: Term[String]) => forall((j: Term[String]) => j === k || bumps(m, k).get(j) === m.get(j))))
val bump = Node.contract(bumps)("A bump adds one to its name's count, and leaves the others.", why = "Per call.")(
  (m, k, r) => r.get(k) === Some(m.getOrElse(k, BigInt(0)) + 1) && r.removed(k) === m.removed(k)).refines(counts)
  .examples()(
    allows(Map("a" -> BigInt(1)), "a", Map("a" -> BigInt(2)), "a counted twice"),
    allows(Map("a" -> BigInt(1)), "b", Map("a" -> BigInt(1), "b" -> BigInt(1)), "b counted once, a left"),
    forbids(Map("a" -> BigInt(1)), "b", Map("b" -> BigInt(1)), "a lost"))
val bumped = define { (m: Term[Map[String, BigInt]], k: Term[String]) => m.updated(k, m.getOrElse(k, BigInt(0)) + 1) }

/** Code keeping values at least a floor, whose examples do not reach the boundary (a value equal to the floor). */
val retained = Param[(List[BigInt], BigInt) => List[BigInt]]("the values kept from a list, given the floor")
val floor = Node.claim("A value is kept exactly when it is on the list and not under the floor.", why = "The floor is the rule.")(
  forall((xs: Term[List[BigInt]], f: Term[BigInt]) => retained(xs, f).forall(x => xs.contains(x) && x >= f) && xs.forall(x => x >= f implies retained(xs, f).contains(x))))
val floorKeep = Node.contract(retained)("A call keeps exactly the values of the list not under the floor.", why = "Floor, for one call.")(
  (xs, f, r) => r.forall(x => xs.contains(x) && x >= f) && xs.forall(x => x >= f implies r.contains(x))).refines(floor)
  .examples()(
    allows(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(5)), "the value over the floor"),
    allows(List(BigInt(1)), BigInt(3), Nil, "nothing over the floor"),
    forbids(List(BigInt(1), BigInt(5)), BigInt(3), List(BigInt(1)), "a value under the floor is never kept"))
val keepAtLeast = define { (xs: Term[List[BigInt]], f: Term[BigInt]) => xs.filter(x => x >= f) }

/** Defined functions of four and five arguments, called like the others. */
val pagesBetween = define { (b: Term[Book], lo: Term[Int], hi: Term[Int], title: Term[String]) => b.pages >= lo && b.pages <= hi && b.title =!= title }
val pagesBetweenOn = define { (b: Term[Book], lo: Term[Int], hi: Term[Int], title: Term[String], s: Term[Shelf]) => pagesBetween(b, lo, hi, title) && where(s) =!= title }

/** Code reading a defined term whose definition calls the shelf service: it does not call the service
  * itself, so the service's promise is no hypothesis of its proof.
  */
val pickedFrom = Param[(List[Book], Book) => Boolean]("whether the shelf service picks the book from the shelf")
val pickedFromDef = Node.definition("A book is picked from a shelf when the service picks it, asked for the whole shelf.",
  why = "The service is how books leave the shelf.")(pickedFrom := ((l: Term[List[Book]], b: Term[Book]) => picks(l, l.length).contains(b)))
val viaPickedFrom = define { (shelf: Term[List[Book]], n: Term[Int]) => shelf.filter(b => pickedFrom(shelf, b) && b.pages >= minPages) }
val readsKb = KnowledgeBase("Reads", idea = "IDEA.md")(pickedAgain, Again.again, pickPromise, pickedFromDef)
  .implementProven(pickPromise)(longOnes).implementProven(Again.again)(viaPickedFrom)

/** Membership through a set built once (`toSet`): a hash set in Scala, the list's membership in Lean. */
val kept = Param[(List[Book], List[Book]) => List[Book]]("the picked books a check keeps, those on the shelf")
val keptOnShelf = Node.claim("A book is kept exactly when it was picked and is on the shelf.", why = "Only books of the shelf leave it.")(
  forall((s: Term[List[Book]], p: Term[List[Book]]) => forall((b: Term[Book]) => kept(s, p).contains(b) === (p.contains(b) && s.contains(b)))))
val keep = Node.contract(kept)("A call keeps exactly the picked books that are on the shelf.", why = "KeptOnShelf, for one call.")(
  (s, p, r) => r.forall(b => p.contains(b) && s.toSet.contains(b)) && p.forall(b => s.toSet.contains(b) implies r.contains(b))).refines(keptOnShelf)
  .examples()(
    allows(List(Book("A", 100)), List(Book("A", 100), Book("B", 200)), List(Book("A", 100)), "the book on the shelf"),
    forbids(List(Book("A", 100)), List(Book("B", 200)), List(Book("B", 200)), "never a book off the shelf"),
    forbids(List(Book("A", 100)), List(Book("A", 100)), Nil, "never drops a book on the shelf"))
val keptOnce = define { (shelf: Term[List[Book]], picked: Term[List[Book]]) =>
  let(shelf.toSet)(there => picked.filter(b => there.contains(b)))
}
val keepKb = KnowledgeBase("Keep", idea = "IDEA.md")(keptOnShelf, keep).implementProven(keep)(keptOnce)

/** A root of two conjuncts in general terms, and parts that each say one of them again with the definition applied
  * (folded), or say more than it (refined).
  */
val worthy = Param[Book => Boolean]("whether a book is worth handing out")
val worth = Node.definition("A book is worth handing out when it has at least 100 pages.", why = "Readers asked for long books.")(
  worthy := ((b: Term[Book]) => b.pages >= 100))
val handedOut = Node.claim("Picked books come from the shelf and are worth handing out.", why = "What the shelf hands out.")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b))) && forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => worthy(b))))
val fromShelfAgain = Node.claim("Every picked book is on the shelf.", why = "w")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b)))).refines(handedOut)
val hundredPages = Node.claim("Every picked book has at least 100 pages.", why = "w")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => b.pages >= 100))).refines(handedOut)
val fromShelfOnce = Node.claim("Picked books come from the shelf, and no more are picked than it holds.", why = "w")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b)) && picks(l, n).length <= l.length)).refines(handedOut)
val twoHundredPages = Node.claim("Every picked book has at least 200 pages.", why = "w")(
  forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => b.pages >= 200))).refines(handedOut)
def handedOutKb(parts: Node[?]*): KnowledgeBase = KnowledgeBase("HandedOut", idea = "IDEA.md")((handedOut +: worth +: parts)*)
