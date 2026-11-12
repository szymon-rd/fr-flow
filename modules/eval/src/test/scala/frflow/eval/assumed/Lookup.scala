package frflow.eval.assumed

import cats.effect.{IO, Ref}
import frflow.*

/** An operation known only by its assumptions (G2): a register of numbers whose index lookup, `has`, is given no
  * steps, only what is assumed of it (it answers whether the register holds the number, and changes nothing). A
  * program puts a number unless the index has it; the register never holds a number twice. With only half the
  * answer assumed (`hasSound`: a yes is right), the program is still shown to store the number, but not to keep the
  * rule: it relies on more than the assumption says, and stays unproven.
  */
object Lookup:
  val put = Declaration[BigInt => Flow[Unit]]("a number put in the register, at its end")
  val has = Declaration[BigInt => Flow[Boolean]]("whether the register's index holds a number")

  object register extends StateModel[List[BigInt]]("the numbers in the register, oldest first"):
    put.means(n => state.update(xs => xs :+ n))
    has.assumed

  val putOnce = Declaration[BigInt => Flow[Unit]]("a number put in the register unless its index holds it")
  val putOnceCode = program { (n: Term[BigInt]) =>
    for
      held <- has(n)
      _    <- Flow.when(!held)(put(n))
    yield () }

  val registerOnly = Node.assumption("Nothing but the programs change the register.")(register.onlyCodeChanges)
  val registerOne = Node.assumption("One run at a time on the register.")(register.atomic)
  val startsEmpty = Node.assumption("The register starts empty.")(register.initially(xs => xs === Nil))

  val hasAnswers = Node.assumption("The index has a number exactly when the register holds it.")(
    forall((n: Term[BigInt]) => has(n).result === register.current.contains(n)))
  val hasSound = Node.assumption("The index has a number only when the register holds it.")(
    forall((n: Term[BigInt]) => has(n).result implies register.current.contains(n)))
  val hasKeeps = Node.assumption("Looking a number up changes nothing.")(
    forall((n: Term[BigInt]) => register.in(has(n).after) === register.current))

  val noDuplicates = Node.claim("The register never holds a number twice.")(
    always(register)(xs => xs.pairwise((a, b) => a =!= b))).assuming(registerOnly, registerOne, startsEmpty)
  val putOnceStores = Node.claim("After putting a number once, the register holds it.")(
    forall((n: Term[BigInt]) => register.in(putOnce(n).after).contains(n))).assuming(registerOne)

  /** The register in memory: `forgets`, the seeded bug, has an index that never has a number. */
  final class Indexed(r: Ref[IO, List[BigInt]], forgets: Boolean):
    def put(n: BigInt): IO[Unit] = r.update(_ :+ n)
    def has(n: BigInt): IO[Boolean] = if forgets then IO.pure(false) else r.get.map(_.contains(n))
    def numbers: IO[List[BigInt]] = r.get
  object Indexed:
    def holding(xs: List[BigInt], forgets: Boolean = false): IO[Indexed] = Ref[IO].of(xs).map(Indexed(_, forgets))

  /** Two lookups of equal numbers answer alike: two runs of `has` in one statement, which no run of it reads. */
  val hasAlike = Node.assumption("The index answers alike for equal numbers.")(
    forall((n: Term[BigInt], m: Term[BigInt]) => (m === n) implies (has(m).result === has(n).result)))

  private def registers(answer: Node*) = FrModel("Registers")((List(noDuplicates, putOnceStores, registerOnly,
    registerOne, startsEmpty) ++ answer :+ hasKeeps)*)
    .defining(putOnce.define(putOnceCode))
    .defining(defineOperations(put, has)(start = Indexed.holding(_), observe = _.numbers)(i => (i.put, i.has)))

  /** The index assumed to answer exactly: the rule kept, the number stored. */
  val knowledge: FrModel = registers(hasAnswers)
  /** The index assumed only to be right when it says yes: the rule not shown kept. */
  val halfAssumed: FrModel = registers(hasSound)
  /** The index assumed to answer exactly, and alike for equal numbers, which the runs cannot evaluate. */
  val alike: FrModel = registers(hasAnswers, hasAlike)
