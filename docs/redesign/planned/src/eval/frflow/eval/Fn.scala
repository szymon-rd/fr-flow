package frflow.eval

/** Every cast between the developer's typed Scala functions and the untyped values the IR is run on, each typed by
  * the IR (a call of an operation of type `F` has `F`'s arity; a `Bool` is a `Boolean`; a view gives pairs).
  */
object Fn:
  def bool(v: ScalaValue): Boolean = v.unwrap.asInstanceOf[Boolean]

  def pairs(v: ScalaValue): List[(ScalaValue, ScalaValue)] =
    v.unwrap.asInstanceOf[List[(Any, Any)]].map((a, b) => (ScalaValue(a), ScalaValue(b)))

  /** A Scala function of `args.size` inputs called on them. */
  def call(f: AnyRef, args: List[ScalaValue]): ScalaValue = ScalaValue((f, args.map(_.unwrap)) match
    case (g: Function0[?], Nil)                           => g()
    case (g: Function1[Any, Any] @unchecked, List(a))     => g(a)
    case (g: Function2[Any, Any, Any] @unchecked, List(a, b)) => g(a, b)
    case (g: Function3[Any, Any, Any, Any] @unchecked, List(a, b, c)) => g(a, b, c)
    case _ => throw IllegalStateException(s"FrFlow bug: a function called on ${args.size} inputs")) // … to 6

  /** A function of `arity` inputs, typed `F`, running `body` on its inputs. */
  def of[F](arity: Int)(body: List[ScalaValue] => ScalaValue): F = (arity match
    case 0 => () => body(Nil).unwrap
    case 1 => (a: Any) => body(List(ScalaValue(a))).unwrap
    case 2 => (a: Any, b: Any) => body(List(a, b).map(ScalaValue(_))).unwrap
    case 3 => (a: Any, b: Any, c: Any) => body(List(a, b, c).map(ScalaValue(_))).unwrap
    case _ => throw IllegalStateException(s"FrFlow bug: an operation of $arity inputs") // … to 6
  ).asInstanceOf[F]
