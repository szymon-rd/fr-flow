package frflow

/** Values near the examples': what a probe tries, in Scala and in Lean, so the translation is checked
  * where the examples do not reach, and production code runs on data the examples do not give.
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

  /** Values of the same type near `v`: a number at the boundaries (`nums`, and next to it), a list
    * emptied, shortened, reversed, with its head again or with a row like its head added, a string emptied, an option empty, a case
    * class or tuple with one field changed so. What the examples do not reach, the translation is
    * checked on.
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
      case p: Product if p.productArity > 0 =>
        val fields = p.productIterator.toList
        val make = p.getClass.getConstructors.find(_.getParameterCount == fields.size)
        make.toList.flatMap(k => fields.indices.flatMap(i => near(fields(i), nums).take(3).flatMap(x =>
          scala.util.Try(k.newInstance(fields.updated(i, x).map(_.asInstanceOf[AnyRef])*)).toOption)))
      case _ => Nil
    out.distinct.filter(_ != v)
