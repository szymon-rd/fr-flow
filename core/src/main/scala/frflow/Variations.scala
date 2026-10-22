package frflow

import scala.collection.mutable

/** Calls no example makes, made from the examples' own values: a value at one place of an example
  * (an input, a parameter's value, a field of a record, an element of a list) is replaced by another
  * value seen at that place, a list loses, gains or reorders elements, an option becomes empty. A
  * value keeps the type of its place, so Scala runs the call and Lean can state it. The same
  * examples give the same calls.
  */
object Variations:
  /** A call: the parameter values, and the two inputs. */
  final case class Call(bindings: List[Binding], a: Any, b: Any, from: Int)

  def of(cases: List[Example], count: Int, seed: Long = 7): List[Call] =
    if cases.isEmpty || count <= 0 then Nil
    else
      val pool = mutable.LinkedHashMap.empty[String, mutable.LinkedHashSet[Any]]
      def collect(v: Any, place: String): Unit =
        if v != null && !isFunction(v) then
          pool.getOrElseUpdate(place, mutable.LinkedHashSet.empty) += v
          v match
            case xs: List[?]  => xs.foreach(collect(_, place + "[]"))
            case Some(x)      => collect(x, place + "?")
            case p: Product if p.productArity > 0 => p.productIterator.zipWithIndex.foreach((f, i) => collect(f, s"$place.${p.getClass.getName}.$i"))
            case _            => ()
      def value(b: Binding): Option[Any] =
        if b.table.isDefined then None else scala.util.Try(b.value()).toOption.filterNot(isFunction)
      cases.foreach { e =>
        collect(e.a, "a"); collect(e.b, "b")
        e.bindings.foreach(b => value(b).foreach(collect(_, "param:" + b.param.name)))
      }
      val rnd = scala.util.Random(seed)
      def pick(place: String, like: Any): Option[Any] =
        pool.get(place).map(_.toVector.filter(c => c != like && compatible(like, c))).filter(_.nonEmpty).map(cs => cs(rnd.nextInt(cs.size)))
      def mutate(v: Any, place: String): Any =
        val swap = if rnd.nextInt(3) == 0 then pick(place, v) else None
        swap.getOrElse(v match
          case xs: List[?] =>
            rnd.nextInt(4) match
              case 0 if xs.nonEmpty => xs.patch(rnd.nextInt(xs.size), Nil, 1)
              case 1 => pick(place + "[]", null).orElse(xs.headOption).fold(xs)(x => (x :: xs.reverse).reverse)
              case 2 if xs.size > 1 => rnd.shuffle(xs)
              case _ if xs.nonEmpty =>
                val i = rnd.nextInt(xs.size)
                xs.updated(i, mutate(xs(i), place + "[]"))
              case _ => xs
          case Some(x) => if rnd.nextInt(3) == 0 then None else Some(mutate(x, place + "?"))
          case None    => pick(place, v).getOrElse(None)
          case p: Product if p.productArity > 0 && !p.isInstanceOf[Tuple] =>
            val i = rnd.nextInt(p.productArity)
            val fields = p.productIterator.toArray
            fields(i) = mutate(fields(i), s"$place.${p.getClass.getName}.$i")
            rebuild(p, fields).getOrElse(p)
          case other => other)
      val known = cases.map(e => (e.a, e.b, e.bindings.map(value))).toSet
      val seen = mutable.LinkedHashMap.empty[Any, Call]
      var tries = 0
      while seen.size < count && tries < count * 20 do
        tries += 1
        val k = rnd.nextInt(cases.size)
        val e = cases(k)
        // One to three places changed: near the examples, so each call reads as one of them varied.
        val changes = 1 + rnd.nextInt(3)
        var (a, b, vals) = (e.a, e.b, e.bindings.map(value))
        for _ <- 1 to changes do
          rnd.nextInt(2 + vals.count(_.isDefined)) match
            case 0 => a = mutate(a, "a")
            case 1 => b = mutate(b, "b")
            case j =>
              val defined = vals.zipWithIndex.collect { case (Some(_), i) => i }
              val i = defined(j - 2)
              vals = vals.updated(i, vals(i).map(mutate(_, "param:" + e.bindings(i).param.name)))
        val key = (a, b, vals)
        if !known(key) && !seen.contains(key) then
          val bs = e.bindings.zip(vals).map((bd, v) => v.fold(bd)(x => bd.copy(value = () => x)))
          seen(key) = Call(bs, a, b, k)
      seen.values.toList

  // (A list or a map is a function too, of its indices or keys: a value, here.)
  private def isFunction(v: Any): Boolean = !v.isInstanceOf[Iterable[?]] && (v.isInstanceOf[Function0[?]] || v.isInstanceOf[Function1[?, ?]] ||
    v.isInstanceOf[Function2[?, ?, ?]] || v.isInstanceOf[Function3[?, ?, ?, ?]] || v.getClass.getName.contains("$$Lambda"))

  /** Values of one place may be of one class, or cases of one enum, or lists, or options. */
  private def compatible(like: Any, c: Any): Boolean =
    if like == null then true
    else (like, c) match
      case (_: List[?], _: List[?]) => true
      case (_: Option[?], _: Option[?]) => true
      case (x: scala.reflect.Enum, y: scala.reflect.Enum) => enumOf(x.getClass) == enumOf(y.getClass)
      case _ => like.getClass == c.getClass

  private def enumOf(c: Class[?]): Class[?] =
    val s = c.getSuperclass
    if s != null && classOf[scala.reflect.Enum].isAssignableFrom(s) then enumOf(s) else c

  /** The same case class (or enum case) with other fields, if it has a constructor taking them. */
  private def rebuild(p: Product, fields: Array[Any]): Option[Any] =
    p.getClass.getConstructors.find(_.getParameterCount == fields.length).flatMap { k =>
      scala.util.Try(k.newInstance(fields.map(_.asInstanceOf[AnyRef])*)).toOption
    }
