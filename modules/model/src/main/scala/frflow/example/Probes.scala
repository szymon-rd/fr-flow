package frflow
package example

import scala.util.Try

/** Inputs and values near the examples', shared by Lean's probes and the code's runs. */
object Probes:
  def numbers(v: Any): List[BigInt] = v match
    case i: Int     => List(BigInt(i))
    case l: Long    => List(BigInt(l))
    case b: BigInt  => List(b)
    case l: Iterable[?] => l.toList.flatMap(numbers)
    case Some(x)    => numbers(x)
    case p: Product => p.productIterator.toList.flatMap(numbers)
    case _          => Nil
  def boundaries(cases: List[Example]): List[BigInt] = cases.flatMap(_.inputs.flatMap(numbers)).distinct

  /** Values near `v`: a number at the boundaries and next to them, a list shortened, reversed or grown, a field changed. */
  def near(v: Any, nums: List[BigInt]): List[Any] =
    val out: List[Any] = v match
      case b: Boolean => List(!b)
      case i: Int     => (nums.filter(_.isValidInt).map(_.toInt) ++ List(0, i + 1, i - 1, -i))
      case l: Long    => (nums.filter(_.isValidLong).map(_.toLong) ++ List(0L, l + 1, l - 1, -l))
      case b: BigInt  => nums ++ List(BigInt(0), b + 1, b - 1, -b)
      case s: String  => List("", s + s)
      case Some(x)    => None :: near(x, nums).take(2).map(Some(_))
      case l: List[?] => if l.isEmpty then Nil else List(Nil, l.tail, l.reverse, l.head :: l) ++ near(l.head, nums).take(2).map(x => l :+ x)
      case p: Product if p.productArity > 0 =>
        val fields = p.productIterator.toList
        p.getClass.getConstructors.find(_.getParameterCount == fields.size).toList.flatMap(k => fields.indices.flatMap(i =>
          near(fields(i), nums).take(3).flatMap(x => Try(k.newInstance(fields.updated(i, x).map(_.asInstanceOf[AnyRef])*)).toOption)))
      case _ => Nil
    out.distinct.filter(_ != v)

  /** Inputs near the examples' that no example asks: what Lean probes evaluate. Each input is the example's or one near
    * it, the first input varying slowest.
    */
  def inputs(cases: List[Example]): List[List[Any]] =
    val nums = boundaries(cases)
    val asked = cases.map(_.inputs).toSet
    def calls(choices: List[List[Any]]): List[List[Any]] =
      choices.foldRight(List(List.empty[Any]))((xs, rest) => for x <- xs; r <- rest yield x :: r)
    cases.flatMap(e => calls(e.inputs.map(x => x :: near(x, nums)))).distinct.filterNot(asked)
