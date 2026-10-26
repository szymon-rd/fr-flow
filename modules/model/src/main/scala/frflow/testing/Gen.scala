package frflow
package testing

/** A generator a developer or an agent gives for a type the derived one serves badly: `Gen.oneOf(Path("/a"), Path("/b"))`.
  * What it says it makes is shown beside the results, and the derived generator keeps making a share of the type's
  * values, so a narrow generator never hides the rest.
  */
final class Gen[A] private[frflow] (val describe: String, private[frflow] val draw: Draw => A):
  def map[B](f: A => B): Gen[B] = Gen(describe, d => f(draw(d)))
  def flatMap[B](f: A => Gen[B]): Gen[B] = Gen(describe, d => f(draw(d)).draw(d))
  /** What the generator makes, in the developer's words. */
  def describedAs(text: String): Gen[A] = Gen(text, draw)

object Gen:
  def oneOf[A](first: A, rest: A*): Gen[A] =
    val all = (first +: rest).toVector
    Gen(s"one of ${all.map(Example.show).mkString(", ")}", d => all(d.below(all.size)))
  def choose(lo: Int, hi: Int): Gen[Int] = Gen(s"from $lo to $hi", d => lo + d.below(hi - lo + 1))
  def chooseBig(lo: BigInt, hi: BigInt): Gen[BigInt] =
    Gen(s"from $lo to $hi", d => lo + BigInt(d.below((hi - lo + 1).min(BigInt(Int.MaxValue)).toInt)))
  def listOf[A](g: Gen[A]): Gen[List[A]] = Gen(s"lists of ${g.describe}", d => List.fill(d.length)(g.draw(d)))
  def const[A](a: A): Gen[A] = Gen(Example.show(a), _ => a)
  /** What FrFlow derives from the type. */
  def derived[A](using t: LeanType[A]): Gen[A] = Gen("derived from the type", d => d.value(t).asInstanceOf[A])
