package frflow

import scala.util.Try

/** What to try beyond the examples: the one generator of inputs and values near the examples', for
  * Lean (probes: the translation is checked where the examples do not reach) and for Scala (plain code
  * runs on calls and data the examples do not give).
  */
object Probes:
  /** The numbers a value holds, however nested: the boundaries a probe tries. */
  def numbers(v: Any): List[BigInt] = v match
    case i: Int     => List(BigInt(i))
    case l: Long    => List(BigInt(l))
    case b: BigInt  => List(b)
    case l: Iterable[?] => l.toList.flatMap(numbers)
    case Some(x)    => numbers(x)
    case p: Product => p.productIterator.toList.flatMap(numbers)
    case _          => Nil

  /** The numbers the examples' inputs hold, each once. */
  def boundaries(cases: List[Example]): List[BigInt] = cases.flatMap(e => numbers(e.a) ++ numbers(e.b)).distinct

  /** Values of the same type near `v`: a number at the boundaries (`nums`, and next to it), a list
    * emptied, shortened, reversed, with its head again or with a row like its head added, a string
    * emptied, an option empty, a case class or tuple with one field changed so.
    */
  def near(v: Any, nums: List[BigInt]): List[Any] =
    val out: List[Any] = v match
      case b: Boolean => List(!b)
      case i: Int     => (nums.filter(_.isValidInt).map(_.toInt) ++ List(0, i + 1, i - 1, -i))
      case l: Long    => (nums.filter(_.isValidLong).map(_.toLong) ++ List(0L, l + 1, l - 1, -l))
      case b: BigInt  => nums ++ List(BigInt(0), b + 1, b - 1, -b)
      case s: String  => List("", s + s)
      case Some(x)    => None :: near(x, nums).take(2).map(Some(_))
      case l: List[?] => if l.isEmpty then Nil else List(Nil, l.tail, l.reverse, l.head :: l) ++ near(l.head, nums).take(2).map(x => l :+ x)
      case p: Product if p.productArity > 0 => nearProduct(p, nums)
      case _ => Nil
    out.distinct.filter(_ != v)

  /** A case class or tuple with one field near its value, built through its constructor. */
  private def nearProduct(p: Product, nums: List[BigInt]): List[Any] =
    val fields = p.productIterator.toList
    val make = p.getClass.getConstructors.find(_.getParameterCount == fields.size)
    make.toList.flatMap(k => fields.indices.flatMap(i => near(fields(i), nums).take(3).flatMap(x =>
      Try(k.newInstance(fields.updated(i, x).map(_.asInstanceOf[AnyRef])*)).toOption)))

  /** Inputs near the examples' that no example asks: each example's input or one near it, with its
    * other input or one near that. What Lean probes evaluate.
    */
  def inputs(cases: List[Example]): List[(Any, Any)] =
    val nums = boundaries(cases)
    val asked = cases.map(e => (e.a, e.b)).toSet
    cases.flatMap(e => for { a <- e.a :: near(e.a, nums); b <- e.b :: near(e.b, nums) } yield (a, b)).distinct.filterNot(asked)

  /** Every combination of the examples' inputs: plain code runs on each, not only on the examples'. */
  def combinations(cases: List[Example]): List[(Any, Any)] =
    for a <- cases.map(_.a).distinct; b <- cases.map(_.b).distinct yield (a, b)

  /** Values near a parameter value an example gives (a stored table with a row dropped, repeated or
    * changed): what production code beside a proven define also runs on.
    */
  def variations(v: Any, cases: List[Example]): List[Any] = near(v, boundaries(cases) ++ numbers(v)).take(8)
