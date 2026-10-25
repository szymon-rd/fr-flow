package frflow

/** Scala functions of any arity, as FrFlow handles them inside: an operation's code, a post, a check, a view and a
  * lambda over terms are Scala functions of their inputs (and a result, and a flow's worlds), at most nine arguments.
  * Inside, a call is a list of arguments; at the edges, the user's own `FunctionN`.
  */
private[frflow] object Fn:
  val MaxArity = 9

  /** Calls `f`, a Scala function of `args.size` arguments. */
  def call(f: Any, args: List[Any]): Any = (f, args) match
    case (g: Function0[?], Nil)                                     => g()
    case (g: Function1[Any, ?] @unchecked, List(a))                 => g(a)
    case (g: Function2[Any, Any, ?] @unchecked, List(a, b))         => g(a, b)
    case (g: Function3[Any, Any, Any, ?] @unchecked, List(a, b, c)) => g(a, b, c)
    case (g: Function4[Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d)) => g(a, b, c, d)
    case (g: Function5[Any, Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d, e)) => g(a, b, c, d, e)
    case (g: Function6[Any, Any, Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d, e, h)) => g(a, b, c, d, e, h)
    case (g: Function7[Any, Any, Any, Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d, e, h, i)) => g(a, b, c, d, e, h, i)
    case (g: Function8[Any, Any, Any, Any, Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d, e, h, i, j)) => g(a, b, c, d, e, h, i, j)
    case (g: Function9[Any, Any, Any, Any, Any, Any, Any, Any, Any, ?] @unchecked, List(a, b, c, d, e, h, i, j, k)) =>
      g(a, b, c, d, e, h, i, j, k)
    case _ => throw IllegalArgumentException(s"FrFlow: cannot call $f on ${args.size} arguments")

  /** How many arguments `f` takes, when it is a Scala function. */
  def arity(f: Any): Option[Int] = f match
    case _: Function0[?] => Some(0)
    case _: Function1[?, ?] => Some(1)
    case _: Function2[?, ?, ?] => Some(2)
    case _: Function3[?, ?, ?, ?] => Some(3)
    case _: Function4[?, ?, ?, ?, ?] => Some(4)
    case _: Function5[?, ?, ?, ?, ?, ?] => Some(5)
    case _: Function6[?, ?, ?, ?, ?, ?, ?] => Some(6)
    case _: Function7[?, ?, ?, ?, ?, ?, ?, ?] => Some(7)
    case _: Function8[?, ?, ?, ?, ?, ?, ?, ?, ?] => Some(8)
    case _: Function9[?, ?, ?, ?, ?, ?, ?, ?, ?, ?] => Some(9)
    case _ => None

  /** The Scala function of `n` arguments that runs `g` on them. */
  def of(n: Int)(g: List[Any] => Any): AnyRef = n match
    case 0 => () => g(Nil)
    case 1 => (a: Any) => g(List(a))
    case 2 => (a: Any, b: Any) => g(List(a, b))
    case 3 => (a: Any, b: Any, c: Any) => g(List(a, b, c))
    case 4 => (a: Any, b: Any, c: Any, d: Any) => g(List(a, b, c, d))
    case 5 => (a: Any, b: Any, c: Any, d: Any, e: Any) => g(List(a, b, c, d, e))
    case 6 => (a: Any, b: Any, c: Any, d: Any, e: Any, h: Any) => g(List(a, b, c, d, e, h))
    case 7 => (a: Any, b: Any, c: Any, d: Any, e: Any, h: Any, i: Any) => g(List(a, b, c, d, e, h, i))
    case 8 => (a: Any, b: Any, c: Any, d: Any, e: Any, h: Any, i: Any, j: Any) => g(List(a, b, c, d, e, h, i, j))
    case 9 => (a: Any, b: Any, c: Any, d: Any, e: Any, h: Any, i: Any, j: Any, k: Any) => g(List(a, b, c, d, e, h, i, j, k))
    case _ => throw IllegalArgumentException(s"FrFlow: at most $MaxArity arguments, not $n")
