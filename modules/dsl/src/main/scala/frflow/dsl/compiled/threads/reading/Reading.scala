package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Term as Rocq, Ty}
import frflow.dsl.compiled.threads.known.{Reserved, ThreadUnit}
import frflow.dsl.lifted.NotRead
import scala.quoted.Quotes

/** What every part of the reader of thread programs shares: the trees of the compiled code as its TASTy has them
  * (`q`), the unit read (`unit`), the variables in scope and how each is read (`Env`), what an expression is read
  * for (`Goal`), and what the parts give each other. Each Scala construct read is one construct of `Lang.v`; any
  * other is refused (`NotRead`), and what holds it becomes `chaos` (`ReadMembers`, `ReadInline`).
  */
private[threads] trait Reading:
  val q: Quotes
  import q.reflect.*

  def unit: ThreadUnit
  val catalogue: Catalogue = Catalogue()
  /** Whether `name` names a definition of the file (`ReadSigs`). */
  def defined(name: String): Boolean

  /** How a Scala variable in scope is read. */
  enum Slot:
    /** A value, named `name`. */
    case Local(name: String, ty: Ty)
    /** A `var`, the value threaded through what assigns it; `known`: the name of what it holds, where it is known
      * not to be null.
      */
    case Mutable(name: String, ty: Ty, known: Option[String])
    /** A by-name parameter: a closure, called where it is read. */
    case ByName(name: String)
    /** A parameter of an inline method: its argument, read where the parameter is. */
    case Thunk(tree: Term, env: Env)
    /** A value that may be null, tested for it: held as the option `option`. */
    case Tested(option: String, content: Ty, declared: Ty)
    /** A local method: the `var`s it reads or assigns are its first arguments, those it assigns what it gives. */
    case Method(name: String, vars: List[Symbol], assigns: List[Symbol])

  /** The variables in scope (`vars`), the Rocq names bound to them with their types (`locals`), `this` where a
    * method is read (`self`: its fields by name, and itself), for an exception caught, what reads each of its
    * arguments (`caught`: by the variable and the method), and the `var`s in the order they are declared.
    */
  final case class Env(vars: Map[Symbol, Slot], locals: Map[String, Ty], self: Option[Self],
      caught: Map[(Symbol, String), String], declared: List[Symbol]):
    def +(bound: (Symbol, Slot)): Env = copy(vars = vars + bound)
    def local(name: String, ty: Ty): Env =
      if Reserved.free(name) && !defined(name) then copy(locals = locals.updated(name, ty))
      else refuse(s"a variable named $name, which names something else in the Rocq")
    def named(sym: Symbol, name: String, ty: Ty): Env = (this + (sym -> Slot.Local(name, ty))).local(name, ty)

  /** `this` in a method: the class, the value it is, and what reads each field. */
  final case class Self(cls: Symbol, value: Res, fields: Map[String, Res])

  /** What an expression is read for. */
  enum Goal:
    /** Its value, at the type it has. */
    case Value
    /** Its value, at `ty`. */
    case As(ty: Ty)
    /** The values the `var`s `vars` have after it. */
    case State(vars: List[Symbol])
    /** The turn of a loop a tail-recursive method `self` is: its next arguments, or its result. */
    case Loop(self: Symbol)

  /** An expression read for a goal: a program, and the type of what it gives. */
  final case class Done(term: Rocq, ty: Ty)

  /** An expression's value, as the steps before it and a term (`ReadExprs`). */
  def expr(t: Term)(using Env): Res
  /** An expression read for `goal`, as one program (`ReadControl`). */
  def tail(t: Term, goal: Goal)(using Env): Done
  /** An expression read for `goal`, as the statements it starts with and the program that ends it. */
  def stepped(t: Term, goal: Goal)(using Env): (List[Step], Done)
  /** `r` at type `to` (`Coercions`). */
  def coerce(r: Res, to: Ty)(using Env): Res

  def refuse(what: String): Nothing = throw NotRead(what)

  /** Code that is not read. */
  def chaos(what: String): Rocq = Rocq.of("chaos", Rocq.Text(what))

  /** A name for a value the Scala does not name: `e` for an exception, else `x`; a numbered one where a variable
    * in scope, or `avoid`, has it.
    */
  def fresh(ty: Ty, avoid: Set[String])(using env: Env): String =
    val taken = env.locals.keySet ++ avoid
    (if ty == Ty.Exn then List("e", "x") else List("x")).find(!taken(_)).orElse(numbered(avoid, 1).headOption)
      .getOrElse(refuse("a value with no name left for it"))

  /** `count` names `x1`, `x2`, … that no variable in scope, or `avoid`, has. */
  def numbered(avoid: Set[String], count: Int)(using env: Env): List[String] =
    LazyList.from(1).map(i => s"x$i").filterNot(env.locals.keySet ++ avoid).take(count).toList

  /** `r` as a value: a program is run first, and what it gives named `name`. */
  def valueAs(r: Res, name: String): Res =
    if r.isValue then r else Res(r.steps :+ Step.Bind(name, r.term), Rocq.Ref(name), r.ty, Res.Kind.Value)

  def value(r: Res)(using Env): Res = valueAs(r, fresh(r.ty, Set.empty))

  /** Several expressions as values, in the order they are evaluated: the one program among them gives `x`,
    * several give `x1`, `x2`, …; a name is passed over if a value read before, or anything read after, mentions it.
    */
  def values(parts: List[Res])(using Env): (List[Step], List[Rocq]) =
    val several = parts.count(!_.isValue) > 1
    val named = parts.zipWithIndex.foldLeft((List.empty[Res], Set.empty[String])) { case ((done, chosen), (r, i)) =>
      if r.isValue then (done :+ r, chosen)
      else
        val avoid = chosen ++ parts.zipWithIndex.flatMap((p, j) => kept(p, i, j))
        val name = if several then fresh(Ty.Never, avoid ++ Set("x", "e")) else fresh(r.ty, avoid)
        (done :+ valueAs(r, name), chosen + name) }._1
    (named.flatMap(_.steps), named.map(_.term))

  /** The names of part `j` a name given to part `i` must not hide. */
  private def kept(p: Res, i: Int, j: Int): List[String] =
    if j > i then p.mentions else if j < i && p.isValue then p.term.mentions else Nil
