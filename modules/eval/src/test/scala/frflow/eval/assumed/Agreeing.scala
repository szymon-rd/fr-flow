package frflow.eval.assumed

import cats.effect.{IO, Ref}
import frflow.*

/** The step 13c review's probe of a program relying on an operation known only by assumptions being a function of its
  * model's state (G2): two lookups of a number agree, with only `hasKeeps` assumed of the lookup. In Lean it holds, so
  * the Scala must be a function of the register's state too: a lookup that flips a coin passes every assumption, and
  * the model tests' second call from the same state catches it.
  */
object Agreeing:
  import Lookup.{has, registerOne, registerOnly, hasKeeps, put}

  val agree = Declaration[BigInt => Flow[Boolean]]("whether two lookups of a number agree")
  val agreeCode = program { (n: Term[BigInt]) =>
    for
      a <- has(n)
      b <- has(n)
    yield a === b }
  val lookupsAgree = Node.claim("Two lookups of a number agree.")(forall((n: Term[BigInt]) => agree(n).result))
    .assuming(registerOne)

  /** The register in memory, its lookup a coin flip that keeps the register. */
  final class Coin(r: Ref[IO, List[BigInt]]):
    def put(n: BigInt): IO[Unit] = r.update(_ :+ n)
    def has(@annotation.unused n: BigInt): IO[Boolean] = IO(scala.util.Random.nextBoolean())
    def numbers: IO[List[BigInt]] = r.get
  object Coin:
    def holding(xs: List[BigInt]): IO[Coin] = Ref[IO].of(xs).map(Coin(_))

  val knowledge: FrModel = FrModel("Twice")(lookupsAgree, registerOne, hasKeeps, registerOnly)
    .defining(agree.define(agreeCode))
    .defining(defineOperations(put, has)(start = Coin.holding, observe = _.numbers)(c => (c.put, c.has)))
