package frflow.proof.rocq.threads

import frflow.core.threads.{Arm, Binder, Pattern, Term, Ty}

/** Rocq's text of a term of a thread program (`core.threads.Term`), and of a type. A term is written on one line
  * where it fits; statements (`x <- m ;;`, `let … in`) each start a line. Parentheses are those Rocq needs: an
  * argument that is not a name, a program bound that is not an application or a `match`.
  */
private[threads] object PrintTerm:
  private val Width = 110

  /** Where a term stands: on its own, as the program a statement binds, or as an argument. */
  enum Place:
    case Top, Bound, Arg

  /** Whether the first arm of a `match` has a bar: the definitions read have, the casts are written without. */
  enum Bars:
    case Leading, Inner

  def ty(t: Ty): String = t match
    case Ty.Named(name)    => name
    case Ty.Of(ctor, arg)  => s"$ctor ${atom(arg)}"
    case Ty.Prod(parts)    => parts.map(factor).mkString(" * ")
    case Ty.Sum(l, r)      => s"${factor(l)} + ${factor(r)}"

  /** A type as an argument. */
  def atom(t: Ty): String = t match
    case Ty.Named(name) => name
    case other          => s"(${ty(other)})"

  private def factor(t: Ty): String = t match
    case Ty.Prod(_) | Ty.Sum(_, _) => s"(${ty(t)})"
    case other                     => ty(other)

  def binder(b: Binder): String = b match
    case Binder.Typed(name, of) => s"($name : ${ty(of)})"
    case Binder.Bare(name, of)  => s"$name : ${ty(of)}"
    case Binder.Plain(name)     => name

  def pattern(p: Pattern): String = p match
    case Pattern.Var(name)        => name
    case Pattern.Ctor(name, Nil)  => name
    case Pattern.Ctor(name, args) => (name :: args.map {
      case c @ Pattern.Ctor(_, _ :: _) => s"(${pattern(c)})"
      case other                       => pattern(other) }).mkString(" ")

  private def parens(t: Term, at: Place): Boolean = (t, at) match
    case (_, Place.Top)                                                        => false
    case (Term.Ref(_) | Term.At(_, _) | Term.Text(_) | Term.Num(_), _)         => false
    case (Term.Tuple(_) | Term.Items(_), _)                                    => false
    case (Term.App(_, _) | Term.Match(_, _), Place.Bound)                      => false
    case _                                                                     => true

  /** The term on one line. */
  def flat(t: Term, at: Place)(using Bars): String = if parens(t, at) then s"(${bare(t)})" else bare(t)

  private def bare(t: Term)(using bars: Bars): String = t match
    case Term.Ref(name)                          => name
    case Term.App(Term.Ref("cons"), List(h, tl)) => s"${flat(h, Place.Arg)} :: ${flat(tl, Place.Arg)}"
    case Term.App(Term.Ref("Z.eqb"), args)       => ("Z.eqb" :: args.map(number)).mkString(" ")
    case Term.App(f, args)                       => (f :: args).map(flat(_, Place.Arg)).mkString(" ")
    case Term.At(name, of)                       => s"(@$name ${atom(of)})"
    case Term.Text(value)                        => "\"" + value + "\""
    case Term.Num(value)                         => s"$value%Z"
    case Term.Tuple(parts)                       => parts.map(flat(_, Place.Bound)).mkString("(", ", ", ")")
    case Term.Items(items)                       => items.map(flat(_, Place.Bound)).mkString("[", "; ", "]")
    case Term.Fun(bs, body)                      => s"fun ${bs.map(binder).mkString(" ")} => ${flat(body, Place.Top)}"
    case Term.Let(n, v, body)                    => s"let $n := ${flat(v, Place.Top)} in ${flat(body, Place.Top)}"
    case Term.Unpack(ns, v, body)                =>
      s"let (${ns.mkString(", ")}) := ${flat(v, Place.Top)} in ${flat(body, Place.Top)}"
    case Term.Bind(n, first, rest)               => s"$n <- ${flat(first, Place.Bound)} ;; ${flat(rest, Place.Top)}"
    case Term.If(c, y, n)                        =>
      s"if ${flat(c, Place.Top)} then ${flat(y, Place.Top)} else ${flat(n, Place.Top)}"
    case Term.Match(on, arms)                    => s"match ${flat(on, Place.Top)} with " +
      (if bars == Bars.Leading then "| " else "") + arms.map(arm).mkString(" | ") + " end"
    case Term.Closure(_, _)                      => "(* a closure with no name *)"

  private def arm(a: Arm)(using Bars): String = s"${pattern(a.pattern)} => ${flat(a.body, Place.Top)}"

  /** An integer where Rocq knows one is meant: an operand of `Z.eqb`. */
  private def number(t: Term)(using Bars): String = t match
    case Term.Num(value) => value.toString
    case other           => flat(other, Place.Arg)

  private def pad(n: Int): String = " " * n

  /** A statement always starts a line; so does a `match` with a bar before each arm. */
  private def breaks(t: Term)(using bars: Bars): Boolean = t match
    case Term.Bind(_, _, _) | Term.Let(_, _, _) | Term.Unpack(_, _, _) => true
    case Term.Match(_, _)                                              => bars == Bars.Leading
    case _                                                             => false

  /** The term, on as many lines as it takes; the lines after the first start `indent` columns in. */
  def lines(t: Term, at: Place, indent: Int)(using Bars): String =
    val one = flat(t, at)
    if indent + one.length <= Width && !(breaks(t) && at == Place.Top) then one
    else if parens(t, at) then s"(${broken(t, indent + 1)})"
    else broken(t, indent)

  /** `body` after ` =>` or `else`: on the same line if it fits, on the next otherwise. */
  private def under(body: Term, indent: Int)(using Bars): String =
    val one = flat(body, Place.Top)
    if indent + one.length <= Width && !breaks(body) then s" $one"
    else s"\n${pad(indent)}${lines(body, Place.Top, indent)}"

  private def broken(t: Term, in: Int)(using Bars): String = t match
    case Term.Bind(n, first, rest) =>
      s"$n <- ${lines(first, Place.Bound, in + 2)} ;;\n${pad(in)}${lines(rest, Place.Top, in)}"
    case Term.Let(n, v, body)      => s"let $n :=${under(v, in + 2)} in\n${pad(in)}${lines(body, Place.Top, in)}"
    case Term.Unpack(ns, v, body)  =>
      s"let (${ns.mkString(", ")}) := ${lines(v, Place.Top, in + 2)} in\n${pad(in)}${lines(body, Place.Top, in)}"
    case Term.If(c, y, n)          =>
      s"if ${flat(c, Place.Top)} then${under(y, in + 2)}\n${pad(in)}else${under(n, in + 2)}"
    case Term.Match(on, arms)      => s"match ${flat(on, Place.Top)} with\n" + arms.map(a =>
      s"${pad(in)}| ${pattern(a.pattern)} =>${under(a.body, in + 4)}").mkString("\n") + s"\n${pad(in)}end"
    case Term.Fun(bs, body)        => s"fun ${bs.map(binder).mkString(" ")} =>${under(body, in + 2)}"
    case Term.App(f, args) if f != Term.Ref("cons") && f != Term.Ref("Z.eqb") => applied(f, args, in)
    case other                     => flat(other, Place.Top)

  /** An application: each argument on the line while it fits, on a line of its own otherwise. */
  private def applied(f: Term, args: List[Term], in: Int)(using Bars): String =
    args.foldLeft(flat(f, Place.Arg)) { (text, a) =>
      val column = if text.contains('\n') then text.length - text.lastIndexOf('\n') - 1 else in + text.length
      val one = flat(a, Place.Arg)
      if column + 1 + one.length <= Width then s"$text $one"
      else s"$text\n${pad(in + 2)}${lines(a, Place.Arg, in + 2)}" }
