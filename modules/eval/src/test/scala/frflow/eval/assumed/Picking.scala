package frflow.eval.assumed

import cats.effect.{IO, Ref}
import frflow.*

/** The step 13c review's probes of a result from outside (G2, owner §37): a register whose `pick` gives a `Pos`,
  * known only by what is assumed of it (it changes nothing, `pickKeeps`), its Scala giving `Pos(-1)`; a program taking
  * what it picks (`take`), one handing it to the register's `keep` (`pass`). Nothing proves a picked number positive.
  */
object Picking:
  final case class Pos(v: BigInt) derives LeanType

  val put = Declaration[BigInt => Flow[Unit]]("a number put in the register")
  val keep = Declaration[Pos => Flow[Unit]]("a positive number's value put in the register")
  val pick = Declaration[Flow[Pos]]("a number picked from outside")

  object register extends StateModel[List[BigInt]]("the numbers in the register"):
    put.means(n => state.update(xs => xs :+ n))
    keep.means(p => state.update(xs => xs :+ p.v))
    pick.assumed

  val take = Declaration[Flow[Pos]]("a picked number, taken")
  val takeCode = program { for p <- pick yield p }
  val pass = Declaration[Flow[Unit]]("a picked number, kept in the register")
  val passCode = program { for p <- pick; _ <- keep(p) yield () }

  val registerOne = Node.assumption("One run at a time on the register.")(register.atomic)
  val registerOnly = Node.assumption("Nothing but the programs change the register.")(register.onlyCodeChanges)
  val pickKeeps = Node.assumption("Picking changes nothing.")(register.in(pick.after) === register.current)

  val pickedPositive = Node.claim("A picked number is positive.")(!(pick.result.v <= BigInt(0)))
  val takenPositive = Node.claim("A taken number is positive.")(!(take.result.v <= BigInt(0))).assuming(registerOne)
  val posFromOutside = Node.assumption("Every Pos from outside is positive.")(always[Pos](p => !(p.v <= BigInt(0))))

  /** The register in memory, its `pick` giving a negative number. */
  final class Negative(r: Ref[IO, List[BigInt]]):
    def put(n: BigInt): IO[Unit] = r.update(_ :+ n)
    def keep(p: Pos): IO[Unit] = r.update(_ :+ p.v)
    def pick: IO[Pos] = IO.pure(Pos(-1))
    def numbers: IO[List[BigInt]] = r.get

  private def coded(kb: FrModel): FrModel = kb.defining(defineOperations(put, keep, pick)(
    start = (xs: List[BigInt]) => Ref[IO].of(xs).map(Negative(_)), observe = _.numbers)(c => (c.put, c.keep, c.pick)))

  /** Picked2: a claim of always on what `pick` gives, below the claim that a picked number is positive. */
  object Ruled:
    val posRule = Node.claim("Every Pos is positive.")(always[Pos](p => !(p.v <= BigInt(0)))).refines(pickedPositive)
    val knowledge: FrModel = coded(FrModel("Picked2")(pickedPositive, posRule, pickKeeps, registerOnly))

  /** Picked: the same rule below a claim about `take` too, whose `made_take` once took the claim about `pick`. */
  object Circle:
    val posRule = Node.claim("Every Pos is positive.")(always[Pos](p => !(p.v <= BigInt(0))))
      .refines(pickedPositive, takenPositive)
    val knowledge: FrModel = coded(FrModel("Picked")(pickedPositive, takenPositive, posRule, registerOne, pickKeeps,
      registerOnly)).defining(take.define(takeCode))

  /** A claim about `take` and, apart, one about `pick`: the program relies on what is assumed of `pick` only. */
  val apart: FrModel = coded(FrModel("Apart")(takenPositive, pickedPositive, registerOne, pickKeeps, registerOnly))
    .defining(take.define(takeCode))

  /** The claim about `pick` a part of the claim about `take`: proven from the part, the part proven of nothing. */
  object AsPart:
    val pickedPositive = Node.claim("A picked number is positive.")(!(pick.result.v <= BigInt(0)))
      .refines(takenPositive)
    val knowledge: FrModel = coded(FrModel("AsPart")(takenPositive, pickedPositive, registerOne, pickKeeps,
      registerOnly)).defining(take.define(takeCode))

  /** The claim about `pick` alone. */
  val lone: FrModel = coded(FrModel("Lone")(pickedPositive, pickKeeps, registerOnly))

  /** Claims about `put` alone: one false (the register left empty), one true (it holds the number). A statement's
    * run of an operation with steps is not read as its steps yet, so neither is proven.
    */
  val putEmpties = Node.claim("Putting a number leaves the register empty.")(
    forall((n: Term[BigInt]) => register.in(put(n).after) === (Nil: Term[List[BigInt]])))
  val putHolds = Node.claim("Putting a number, the register holds it.")(
    forall((n: Term[BigInt]) => register.in(put(n).after).contains(n)))
  val puts: FrModel = coded(FrModel("Puts")(putEmpties, putHolds, pickKeeps, registerOnly))

  /** `pass` hands what it picks to `keep`, with a claim and an assumption of always on `Pos` (no theory to validate:
    * the claim is refused there, `AssumedMakes`).
    */
  object Handed:
    val posRule = Node.claim("Every Pos is positive.")(always[Pos](p => !(p.v <= BigInt(0))))
    val passes = Node.claim("Passing keeps the register's numbers.")(register.current.forall(n =>
      register.in(pass.after).contains(n))).assuming(registerOne)
    val knowledge: FrModel = coded(FrModel("Handed")(passes, posRule, posFromOutside, registerOne, pickKeeps,
      registerOnly)).defining(pass.define(passCode))
