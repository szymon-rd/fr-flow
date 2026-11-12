package frflow.core.threads

/** A term of the language thread programs are written in (`Lang.v`): a pure value or a program (`M A`), told
  * apart by its type alone, as in Rocq. A name is a variable in scope or a constant of the library (`ret`, `call`,
  * `try_catch`, an operation of the JDK); the meaning of each constant is the library's.
  *
  * `Closure` is a closure as the code read makes one, before it is given a name: `Closures` replaces each by a
  * constructor of `code` over the variables it captures (`body` is what it runs, given `arg`).
  */
enum Term:
  case Ref(name: String)
  case App(fn: Term, args: List[Term])
  /** A constant whose type Rocq cannot find, given it: `(@nil tid)`. */
  case At(name: String, ty: Ty)
  case Text(value: String)
  /** An integer: `0%Z`. */
  case Num(value: BigInt)
  case Tuple(parts: List[Term])
  case Items(items: List[Term])
  case Fun(binders: List[Binder], body: Term)
  case Let(name: String, value: Term, body: Term)
  /** `let (a, b) := value in body`. */
  case Unpack(names: List[String], value: Term, body: Term)
  /** `name <- first ;; rest`. */
  case Bind(name: String, first: Term, rest: Term)
  case If(cond: Term, yes: Term, no: Term)
  case Match(on: Term, arms: List[Arm])
  case Closure(captured: List[Param], body: Term)

  /** The names this term mentions and does not bind (variables in scope, constants, the constructors of its
    * patterns), each once, in the order it first mentions them.
    */
  def mentions: List[String] = Term.mentioned(this).distinct

object Term:
  /** What a closure is called with. */
  val Arg: String = "arg"

  /** A constant applied; with no argument, the constant. */
  def of(name: String, args: Term*): Term = if args.isEmpty then Ref(name) else App(Ref(name), args.toList)
  def ret(value: Term): Term = of("ret", value)
  val unit: Term = Ref("tt")
  def tuple(parts: List[Term]): Term = parts match
    case Nil      => unit
    case List(of) => of
    case several  => Tuple(several)

  private def mentioned(t: Term): List[String] = t match
    case Ref(n)                  => List(n)
    case App(f, as)              => (f :: as).flatMap(mentioned)
    case At(_, _) | Text(_)      => Nil
    case Num(_)                  => Nil
    case Tuple(ps)               => ps.flatMap(mentioned)
    case Items(is)               => is.flatMap(mentioned)
    case Fun(bs, body)           => without(mentioned(body), bs.map(_.bound))
    case Let(n, v, body)         => mentioned(v) ++ without(mentioned(body), List(n))
    case Unpack(ns, v, body)     => mentioned(v) ++ without(mentioned(body), ns)
    case Bind(n, first, rest)    => mentioned(first) ++ without(mentioned(rest), List(n))
    case If(c, y, n)             => List(c, y, n).flatMap(mentioned)
    case Match(on, arms)         => mentioned(on) ++ arms.flatMap(armed)
    case Closure(_, body)        => without(mentioned(body), List(Arg))

  private def armed(arm: Arm): List[String] =
    constructors(arm.pattern) ++ without(mentioned(arm.body), arm.pattern.bound)

  private def constructors(p: Pattern): List[String] = p match
    case Pattern.Ctor(n, args) => n :: args.flatMap(constructors)
    case Pattern.Var(_)        => Nil

  private def without(names: List[String], bound: List[String]): List[String] = names.filterNot(bound.contains)
