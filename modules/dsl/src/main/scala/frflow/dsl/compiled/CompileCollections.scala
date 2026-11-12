package frflow.dsl.compiled

import frflow.dsl.lifted.LiftOps
import frflow.dsl.term.{Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm

/** The operations of lists, options, maps, sets and pairs the compiler reads: each total, each one operation of
  * the term language. No other is read: `head`, `get` and `apply` are not total.
  */
private[compiled] trait CompileCollections extends Compiling:
  this: Compiler =>
  import q.reflect.*

  private type Many = DTerm[List[Any]]
  private type Maybe = DTerm[Option[Any]]
  private def any(t: DTerm[?]): DTerm[Any] = t.asInstanceOf[DTerm[Any]]
  private val truth: TypeRepr = TypeRepr.of[Boolean]

  def list(c: Calling)(using Env): Option[DTerm[Any]] =
    elementOf(c.on.tpe, ListClass).flatMap(a => joined(c).orElse(asked(c, a)).orElse(mapped(c, a)))

  /** Lists joined, each side read at the list the whole is (`b :: Nil` is a list of `b`'s type). */
  private def joined(c: Calling)(using Env): Option[DTerm[Any]] = elementOf(c.own, ListClass).flatMap { b =>
    def whole(t: Term): Many = read(t, c.own).asInstanceOf[Many]
    (c.name, c.args) match
      case ("++", List(ys)) => Some(any(TermSyntax.++(whole(c.on))(whole(ys))))
      case (":+", List(x))  => Some(any(TermSyntax.:+(whole(c.on))(read(x, b))))
      case ("::", List(x))  => Some(any(LiftOps.cons[Any](read(x, b), whole(c.on))))
      case _                => None
  }

  private def asked(c: Calling, elem: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val xs = read(c.on, c.on.tpe.widen).asInstanceOf[Many]
    lazy val a = spec(elem, c.on)
    def rule(p: Term) = function(p, truth).asInstanceOf[DTerm[Any] => DTerm[Boolean]]
    (c.name, c.args) match
      case ("forall", List(p))   => Some(any(LiftOps.all[Any](xs, hint(p))(rule(p))(using a)))
      case ("exists", List(p))   => Some(any(LiftOps.any[Any](xs, hint(p))(rule(p))(using a)))
      case ("filter", List(p))   => Some(any(LiftOps.filter[Any](xs, hint(p))(rule(p))(using a)))
      case ("find", List(p))     => Some(any(LiftOps.find[Any](xs, hint(p))(rule(p))(using a)))
      case ("contains", List(x)) => Some(any(LiftOps.contains[Any](xs, read(x, elem))))
      case ("isEmpty", Nil)      => Some(any(LiftOps.isEmpty[Any](xs)))
      case ("nonEmpty", Nil)     => Some(any(TermSyntax.unary_!(LiftOps.isEmpty[Any](xs))))
      case _                     => None

  private def mapped(c: Calling, elem: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val xs = read(c.on, c.on.tpe.widen).asInstanceOf[Many]
    lazy val a = spec(elem, c.on)
    (c.name, c.args, elementOf(c.own, ListClass)) match
      case ("map", List(f), Some(b))     =>
        Some(any(LiftOps.map[Any, Any](xs, hint(f))(function(f, b))(using a, spec(b, f))))
      case ("flatMap", List(f), Some(b)) => Some(any(LiftOps.flatMap[Any, Any](xs, hint(f))(
        function(f, c.own).asInstanceOf[DTerm[Any] => Many])(using a, spec(b, f))))
      case ("foldLeft", List(z, f), _)   =>
        val names = hints(f).padTo(2, "x")
        Some(Terms.foldLeft[Any, Any](xs, read(z, c.own), (names(0), names(1)))(function2(f, c.own))(using a))
      case _                             => None

  def option(c: Calling)(using Env): Option[DTerm[Any]] =
    elementOf(c.on.tpe, OptionClass).flatMap(a => held(c, a).orElse(folded(c, a)))

  private def held(c: Calling, elem: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val o = read(c.on, c.on.tpe.widen).asInstanceOf[Maybe]
    lazy val a = spec(elem, c.on)
    def rule(p: Term) = function(p, truth).asInstanceOf[DTerm[Any] => DTerm[Boolean]]
    (c.name, c.args) match
      case ("forall", List(p))             => Some(any(LiftOps.optionAll[Any](o, hint(p))(rule(p))(using a)))
      case ("exists", List(p))             => Some(any(LiftOps.optionAny[Any](o, hint(p))(rule(p))(using a)))
      case ("isDefined" | "nonEmpty", Nil) => Some(any(TermSyntax.isDefined[Any](o)))
      case ("isEmpty", Nil)                => Some(any(LiftOps.isNone[Any](o)(using a)))
      case ("contains", List(x))           => Some(any(LiftOps.optionContains[Any](o, read(x, elem))(using a)))
      case ("getOrElse", List(d))          => Some(LiftOps.orElse[Any](o, read(d, elem)))
      case _                               => None

  private def folded(c: Calling, elem: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val o = read(c.on, c.on.tpe.widen).asInstanceOf[Maybe]
    lazy val a = spec(elem, c.on)
    (c.name, c.args, elementOf(c.own, OptionClass)) match
      case ("map", List(f), Some(b)) =>
        Some(any(LiftOps.optionMap[Any, Any](o, hint(f))(function(f, b))(using a, spec(b, f))))
      case ("fold", List(z, f), _)   =>
        Some(Terms.foldOption[Any, Any](o, read(z, c.own), hint(f))(function(f, c.own))(using a))
      case _                         => None

  /** A map's value at a key, a set's member, a pair's side. Maps and sets are not iterated. */
  def keyed(c: Calling)(using Env): Option[DTerm[Any]] =
    (argsOf(c.on.tpe, MapClass), argsOf(c.on.tpe, SetClass), argsOf(c.on.tpe, PairClass)) match
      case (List(k, v), _, _) => map(c, k, v)
      case (_, List(a), _)    => set(c, a)
      case (_, _, List(a, b)) => side(c, a, b)
      case _                  => None

  private def map(c: Calling, key: TypeRepr, value: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val m = read(c.on, c.on.tpe.widen).asInstanceOf[DTerm[Map[Any, Any]]]
    lazy val v = spec(value, c.on)
    (c.name, c.args) match
      case ("get", List(k))          => Some(any(TermSyntax.get[Any, Any](m)(read(k, key))(using v)))
      case ("contains", List(k))     => Some(any(LiftOps.hasKey[Any, Any](m, read(k, key))(using v)))
      case ("getOrElse", List(k, d)) => Some(LiftOps.valueOr[Any, Any](m, read(k, key), read(d, value)))
      case ("updated", List(k, x))   => Some(any(LiftOps.put[Any, Any](m, read(k, key), read(x, value))))
      case _                         => None

  private def set(c: Calling, elem: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val s = read(c.on, c.on.tpe.widen).asInstanceOf[DTerm[Set[Any]]]
    (c.name, c.args) match
      case ("contains" | "apply", List(x)) => Some(any(LiftOps.member[Any](s, read(x, elem))))
      case ("+" | "incl", List(x))         => Some(any(TermSyntax.incl[Any](s)(read(x, elem))))
      case ("++" | "union", List(t))       =>
        Some(any(TermSyntax.union[Any](s)(read(t, c.on.tpe.widen).asInstanceOf[DTerm[Set[Any]]])))
      case _                               => None

  private def side(c: Calling, a: TypeRepr, b: TypeRepr)(using Env): Option[DTerm[Any]] =
    lazy val p = read(c.on, c.on.tpe.widen).asInstanceOf[DTerm[(Any, Any)]]
    (c.name, c.args) match
      case ("_1", Nil) => Some(TermSyntax._1[Any, Any](p)(using spec(a, c.on)))
      case ("_2", Nil) => Some(TermSyntax._2[Any, Any](p)(using spec(b, c.on)))
      case _           => None

  private def hint(f: Term): String = hints(f).headOption.getOrElse("x")
