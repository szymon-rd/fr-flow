package frflow.fixtures

import frflow.*

/** Operations of one, two and three inputs: a contract on each, code for each, and an invariant kept by a contract of
  * three inputs. What the other fixtures say of two inputs, here of the others.
  */

// One input: a reading clamped at zero.
val clamped = Param[BigInt => BigInt]("the reading the gauge shows for a raw value")
val neverBelowZero = Node.claim("The gauge shows a raw value when it is not negative, and zero otherwise.",
  why = "A negative reading is a sensor fault.")(
  forall((x: Term[BigInt]) => clamped(x) >= 0 && ((x >= 0) implies (clamped(x) === x)) && ((x < 0) implies (clamped(x) === BigInt(0)))))
val clamp = Node.contract("A call shows the raw value when it is not negative, and zero otherwise.",
  why = "NeverBelowZero, for one call.")(forall((x: Term[BigInt]) => clamped(x) >= 0 && ((x >= 0) implies (clamped(x) === x)) && ((x < 0) implies (clamped(x) === BigInt(0))))).refines(neverBelowZero)
  .examples()(
    allows(BigInt(5), BigInt(5), "a positive value is shown"),
    allows(BigInt(-3), BigInt(0), "a negative value shows zero"),
    forbids(BigInt(-3), BigInt(-3), "never a negative reading"))
val clampAtZero = define { (x: Term[BigInt]) => (x >= 0).fold(x, BigInt(0)) }
val clampKb = FrModel("Gauge", idea = "IDEA.md")(neverBelowZero, clamp)

// Three inputs: a member of an access list grants access to another person.
val granted = Param[(List[String], String, String) => List[String]]("the access list after its member (the second) grants access to a person (the third)")
val onlyMembersGrant = Node.claim("A grant keeps everyone on the list, adds the person when the granter is on it, and adds no one else.",
  why = "Access is shared only by those who have it.")(
  forall((acl: Term[List[String]], by: Term[String], who: Term[String]) =>
    acl.forall(x => granted(acl, by, who).contains(x)) && (acl.contains(by) implies granted(acl, by, who).contains(who)) &&
      granted(acl, by, who).forall(x => acl.contains(x) || (x === who && acl.contains(by)))))
val grant = Node.contract("A call keeps everyone on the list, adds the person when the granter is on it, and adds no one else.",
  why = "OnlyMembersGrant, for one call.")(forall((acl: Term[List[String]], by: Term[String], who: Term[String]) => acl.forall(x => granted(acl, by, who).contains(x)) && (acl.contains(by) implies granted(acl, by, who).contains(who)) &&
    granted(acl, by, who).forall(x => acl.contains(x) || (x === who && acl.contains(by))))).refines(onlyMembersGrant)
  .examples()(
    allows(List("ann"), "ann", "bob", List("ann", "bob"), "a member adds bob"),
    allows(List("ann"), "eve", "bob", List("ann"), "someone off the list adds no one"),
    forbids(List("ann"), "eve", "eve", List("ann", "eve"), "never adds a person on their own say"),
    forbids(List("ann", "bob"), "ann", "cid", List("ann", "cid"), "never drops a member"))
val grantIfMember = define { (acl: Term[List[String]], by: Term[String], who: Term[String]) =>
  acl.contains(by).fold(acl ++ List(who), acl)
}
val grantKb = FrModel("Access", idea = "IDEA.md")(onlyMembersGrant, grant)

// Three inputs, and an invariant kept through a view of the call: the books of a shelf between two lengths.
val between = Param[(List[Book], Int, Int) => List[Book]]("the books the shelf service picks between two lengths")
val betweenRoot = Node.claim("Books picked between two lengths come from the shelf and have a length between them.",
  why = "Readers ask for a range.")(
  forall((s: Term[List[Book]], lo: Term[Int], hi: Term[Int]) => between(s, lo, hi).forall(b => s.contains(b) && b.pages >= lo && b.pages <= hi)))
val inStock = Node.invariant[List[Book], Book]("Only books on the shelf are picked.", "Nothing else can be handed out.")(
  (shelf, b) => shelf.contains(b)).refines(betweenRoot)
val pickBetween = Node.contract("A call returns only books of the shelf between the two lengths.",
  why = "Between, for one call.")(forall((shelf: Term[List[Book]], lo: Term[Int], hi: Term[Int]) => between(shelf, lo, hi).forall(b => shelf.contains(b) && b.pages >= lo && b.pages <= hi))).refines(betweenRoot)
  .examples()(
    allows(List(Book("A", 50), Book("B", 150)), 100, 200, List(Book("B", 150)), "the book in the range"),
    allows(List(Book("A", 50), Book("B", 150)), 0, 40, Nil, "none in the range"),
    forbids(List(Book("A", 50)), 0, 100, List(Book("C", 60)), "never a book off the shelf"))
  .keeps(inStock)((shelf, lo, hi, r) => r.map(b => (shelf, b)))
val inRange = define { (shelf: Term[List[Book]], lo: Term[Int], hi: Term[Int]) => shelf.filter(b => b.pages >= lo && b.pages <= hi) }
val betweenKb = FrModel("Between", idea = "IDEA.md")(betweenRoot, pickBetween, inStock).implementProven(pickBetween)(inRange)

// A flow of two inputs: two deliveries restocked, then the stock counted.
val restockBoth = Param[(BigInt, BigInt) => Flow[BigInt]]("a restock of two deliveries: the stock it counts after")
def restockTwo(first: Term[BigInt], second: Term[BigInt]): Flow[BigInt] =
  for
    _ <- stock.add(first)
    _ <- stock.add(second)
    n <- stock.count
  yield n
val stockModel = Node.assumption(stock)(StockModel)("The stock counts the books added to it.", why = "A counter.")
  .implementedBy(c => Counter(c), _.held)
val twoDeliveries = Node.contract(restockBoth)("A restock of two deliveries adds both to the stock, and gives the stock after.", why = "Deliveries are counted as they arrive.")(
  (first, second, r, before, after) => after(StockModel) === before(StockModel) + first + second && r === after(StockModel))
  .examples()(
    allows(BigInt(2), BigInt(3), World(StockModel -> BigInt(10)), BigInt(15), World(StockModel -> BigInt(15)), "both deliveries counted"),
    allows(BigInt(0), BigInt(4), World(StockModel -> BigInt(1)), BigInt(5), World(StockModel -> BigInt(5)), "an empty first delivery"),
    forbids(BigInt(2), BigInt(3), World(StockModel -> BigInt(10)), BigInt(12), World(StockModel -> BigInt(12)), "never only the first"))
/** Beside the gauge: a flow need not refine the root, as a job need not (the CRM's expiry job). */
val deliveriesKb = FrModel("Deliveries", idea = "IDEA.md")(neverBelowZero, clamp, stockModel, twoDeliveries)
  .implementProven(clamp)(clampAtZero).implementProven(twoDeliveries)(restockTwo)

// No input: what the gauge shows now, from the raw reading in force.
val rawReading = Param[BigInt]("the sensor's raw reading now")
val gaugeShows = Param[() => BigInt]("what the gauge shows now")
val showsNow = Node.claim("The gauge shows the raw reading when it is not negative, and zero otherwise.",
  why = "A negative reading is a sensor fault.")(
  gaugeShows() >= 0 && ((rawReading >= 0) implies (gaugeShows() === rawReading)) && ((rawReading < 0) implies (gaugeShows() === BigInt(0))))
val shows = Node.contract("The gauge shows the raw reading when it is not negative, and zero otherwise.",
  why = "ShowsNow, for one reading.")(gaugeShows() >= 0 && ((rawReading >= 0) implies (gaugeShows() === rawReading)) && ((rawReading < 0) implies (gaugeShows() === BigInt(0)))).refines(showsNow)
  .examples(rawReading.bind(5))(allows(BigInt(5), "the raw reading"), forbids(BigInt(0), "never zero for a positive reading"))
  .examples(rawReading.bind(-3))(allows(BigInt(0), "zero for a fault"))
val showRaw = define { () => (rawReading >= 0).fold(rawReading: Term[BigInt], BigInt(0)) }
val gaugeKb = FrModel("Shows", idea = "IDEA.md")(showsNow, shows)

// A flow of no input: the stock counted, left as it was.
val countNow = Param[() => Flow[BigInt]]("a count of the stock: the number it gives")
def countStock(): Flow[BigInt] =
  for n <- stock.count
  yield n
val counting = Node.contract(countNow)("A count gives the stock, and leaves it as it was.", why = "Counting changes nothing.")(
  (r, before, after) => r === before(StockModel) && after(StockModel) === before(StockModel))
  .examples()(
    allows(World(StockModel -> BigInt(5)), BigInt(5), World(StockModel -> BigInt(5)), "five in stock"),
    allows(World(StockModel -> BigInt(2)), BigInt(2), World(StockModel -> BigInt(2)), "two in stock"),
    forbids(World(StockModel -> BigInt(5)), BigInt(5), World(StockModel -> BigInt(0)), "never empties the stock"))
val countingKb = FrModel("Counting", idea = "IDEA.md")(neverBelowZero, clamp, stockModel, counting)
  .implementProven(clamp)(clampAtZero).implementProven(counting)(() => countStock())
