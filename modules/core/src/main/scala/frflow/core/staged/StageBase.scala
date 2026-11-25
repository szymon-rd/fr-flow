package frflow.core.staged

import frflow.core.effect.Idents
import scala.collection.mutable

/** Code the staging does not take: the unit it is in is left to the meaning of its tree. */
final class Unstaged(val why: String) extends RuntimeException(why)

/** What a name in scope is bound to: a value read as it is; one read through what holds it (a `var`, an argument
  * by name); a function made in the code, with its definition.
  */
enum Bound:
  case Plain(v: V)
  case Held(v: V)
  case Made(v: V, d: Tree.DefDef)

  def value: V = this match
    case Plain(v)   => v
    case Held(v)    => v
    case Made(v, _) => v

  def at(v: V): Bound = this match
    case Plain(_)   => Plain(v)
    case Held(_)    => Held(v)
    case Made(_, d) => Made(v, d)

/** The names of one unit's program: each is bound once. */
final class Names:
  private var last = 0

  def fresh(hint: String): String =
    last += 1
    s"${Idents.plain(hint)}_$last"

/** Where a tree is staged: what each key in scope is bound to, the scope the unit was itself given (a variable
  * of the program, looked into when the code runs), and the unit's names.
  */
final case class Env(bound: Map[String, Bound], rest: Option[String], names: Names):
  def having(key: String, b: Bound): Env = copy(bound = bound + (key -> b))
  def havingAll(of: List[(String, Bound)]): Env = copy(bound = bound ++ of)

  /** What a function value or an argument by name made here keeps: every binding, but one that is only what
    * the scope this unit was given holds under the same key, which that scope keeps.
    */
  def kept: Kept =
    val own = bound.toList.sortBy(_._1).map((k, b) => k -> b.value).filterNot((k, v) => rest.exists(v == V.Found(_, k)))
    Kept(own, rest)

  /** The scope of a unit that was given what is kept here, as the variable `scope`. */
  def inside(scope: String, names: Names): Env =
    Env(bound.map((k, b) => k -> b.at(V.Found(scope, k))), Some(scope), names)

/** What every part of the staging shares: the table of what the files define, the units staged so far, and the
  * small steps programs are built of.
  */
private[staged] trait StageBase:
  val table: Defined
  protected val nested: mutable.ListBuffer[StagedUnit] = mutable.ListBuffer.empty
  private var units = 0

  /** The definitions from outside the code calls, each with the arguments it was taken to take unevaluated. */
  val called: mutable.LinkedHashSet[(Sym, List[Boolean])] = mutable.LinkedHashSet.empty

  /** The class whose code is being staged. */
  protected var within: String = ""

  protected def numbered(): Int =
    units += 1
    units

  def refuse(why: String): Nothing = throw Unstaged(why)

  def op(name: String, args: Arg*): P = P.Op(name, args.toList)
  def value(v: V): Arg = Arg.Val(v)
  def variable(name: String): Arg = Arg.Val(V.Var(name))

  /** `of`, then `next` of what it gave. What gives a value without doing anything is that value. */
  def bind(of: P, hint: String)(next: V => P)(using e: Env): P = of match
    case P.Give(v) => next(v)
    case _         =>
      val x = e.names.fresh(hint)
      P.Bind(x, of, next(V.Var(x)))

  /** `of`, then `next`: what `of` gave is dropped. */
  def after(of: P)(next: P): P = of match
    case P.Give(_) => next
    case _         => P.Bind("_", of, next)

  /** Each program in turn, then `next` of what they gave. */
  def each(of: List[P], hint: String)(next: List[V] => P)(using Env): P = of match
    case Nil       => next(Nil)
    case p :: rest => bind(p, hint)(v => each(rest, hint)(vs => next(v :: vs)))

  /** A variable read (`Meaning.read`). */
  def read(key: String)(using e: Env): P = e.bound.get(key) match
    case Some(Bound.Plain(v))                         => P.Give(v)
    case Some(Bound.Made(v, d)) if d.paramss.nonEmpty => P.Give(v)
    case Some(b)                                      => op("held", value(b.value))
    case None                                         =>
      e.rest.fold(P.Stuck(s"a variable that is not in scope: $key"))(sc =>
        op("sought", variable(sc), Arg.Text(key)))
