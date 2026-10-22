package frflow

/** A domain type, open until a definition fixes it (`Node.definition(...)(User := of[UserId])`). Open,
  * it is a type parameter of every Lean definition and theorem that mentions it; defined, a Lean `abbrev`.
  *
  * {{{
  * val User = Opaque("User", "a person with an account")      // use the type as User.T
  * }}}
  *
  * @param means what it stands for in the world: part of the theory
  */
final class Opaque(val name: String, val means: String):
  type T

  /** Fixes this type, in a definition. */
  def :=(t: LeanType): Subst = Subst(name, t.lean, t.types, None, isType = true, this)

/** A domain term of a known type, open until a definition fixes it. Open, it is a Lean binder:
  * everything proven holds for every value of it; defined, a Lean `def` of the vocabulary. It is a fact
  * of the world (`grants`), or an operation of the system (`decide`): a function some contract is about
  * and some code implements, which other code calls through this parameter.
  *
  * {{{
  * val authorized = Param[(User.T, Resource.T) => Boolean]("authorized", "whether the user may access the resource")
  * }}}
  *
  * @param means what it stands for in the world, and where its value comes from: part of the theory
  */
final class Param[A](val name: String, val means: String):

  /** The value bound at run time (see `Node.enforce`). */
  def value: A = Bindings.get(this)

  /** Gives this term a definition, in `Node.definition`. */
  inline def :=[B](inline v: B): Subst = Subst.param(this, Lifted(v))

  /** A run-time value of this parameter; evaluated on every use. */
  def bind(v: => A): Binding = Binding(this, () => v)

  /** A parameter that is a lookup (`K => Option[V]`), given as a finite table: the same function as
    * `bind(table.get)`, and Lean is given the table too, so the examples are evaluated there.
    */
  def bindTable[K, V](table: Map[K, V])(using A =:= (K => Option[V])): Binding = Binding(this, () => table.get, Some(table))

extension [A, R](p: Param[A => R]) def apply(a: A): R = p.value(a)
extension [A, B, R](p: Param[(A, B) => R]) def apply(a: A, b: B): R = p.value(a, b)
extension [A, B, C, R](p: Param[(A, B, C) => R]) def apply(a: A, b: B, c: C): R = p.value(a, b, c)

/** What a definition fixes: an opaque type by a type, or a parameter by a term. `target` is the
  * `Opaque` or `Param` it defines.
  */
final case class Subst(name: String, lean: String, types: List[TypeDecl], term: Option[Lifted[?]], isType: Boolean, target: AnyRef):
  def param: Option[Param[?]] = target match { case p: Param[?] => Some(p); case _ => None }

object Subst:
  def param(p: Param[?], l: Lifted[?]): Subst = Subst(p.name, l.lean, l.types, Some(l), isType = false, p)

/** A Scala type, as a Lean type. */
final case class LeanType(lean: String, types: List[TypeDecl])

/** The Lean translation of a Scala type: `User := of[UserId]`. */
inline def of[T]: LeanType = ${ Lift.leanType[T] }

final case class Binding(param: Param[?], value: () => Any, table: Option[Map[?, ?]] = None)

/** Run-time values of parameters, for the code that evaluates node predicates. */
object Bindings:
  private val current = ThreadLocal.withInitial[Map[String, () => Any]](() => Map.empty)

  def get[A](p: Param[A]): A =
    current.get.get(p.name) match
      case Some(v) => v().asInstanceOf[A]
      case None    => throw IllegalStateException(s"parameter ${p.name} is not bound")

  def within[T](bs: Seq[Binding])(body: => T): T =
    val saved = current.get
    current.set(saved ++ bs.map(b => b.param.name -> b.value))
    try body
    finally current.set(saved)

/** A Lean declaration of a domain type, produced from a Scala case class or enum.
  *
  * @param ctors its constructors (`mk` for a case class, the cases of an enum), each with its fields'
  *              names and Lean types
  */
final case class TypeDecl(name: String, lean: String, uses: List[String], scala: String = "",
    ctors: List[(String, List[(String, String)])] = Nil)

/** A Scala lambda or value together with its Lean translation. Both come from one source.
  *
  * @param params   Lean names and types of the lambda's parameters
  * @param body     the Lean term; `⟦f⟧` marks a call of the defined function `f`
  * @param opaques  opaque types it mentions
  * @param paramRefs parameters it uses, with their Lean types
  * @param valueThunk the Scala value, evaluated on each use (`value`): a term defined by an expression
  *                   over parameters (`sessions := stateAfter(history.value).sessions`) is evaluated
  *                   where it is used, under the bindings in force, not when the model loads
  */
final class Lifted[+F](
    valueThunk: () => F,
    val params: List[(String, String)],
    val result: String,
    val body: String,
    val source: String,
    val types: List[TypeDecl],
    val opaques: List[String],
    val paramRefs: List[(String, String)],
    defsThunk: () => List[Def[?]],
    paramsThunk: () => List[Param[?]],
    opaquesThunk: () => List[Opaque] = () => Nil
):
  /** The Scala value, evaluated now (under the bindings in force). */
  def value: F = valueThunk()
  def defs: List[Def[?]] = defsThunk()
  def paramObjects: List[Param[?]] = paramsThunk()
  def opaqueObjects: List[Opaque] = opaquesThunk()

  def lean: String =
    if params.isEmpty then body else s"fun ${params.map((n, t) => s"($n : $t)").mkString(" ")} => $body"

  def leanType: String = (params.map(_._2) :+ result).mkString(" → ")

object Lifted:
  /** Translates a Scala lambda over the domain. Unsupported Scala is a compile error. */
  inline def apply[F](inline f: F): Lifted[F] = ${ Lift.lifted('f) }

  /** A lambda kept as Scala only, with its source text: for a node that opts out of Lean. */
  inline def informal[F](inline f: F): Lifted[F] = ${ Lift.informal('f) }

  /** Translated when `formal`, kept as Scala only otherwise. */
  inline def of[F](inline formal: Boolean, inline f: F): Lifted[F] =
    inline if formal then apply(f) else informal(f)

  /** The project source files an expression refers to (used to notice implementation changes). */
  inline def sourceFiles(inline x: Any): List[String] = ${ Lift.sourceFiles('x) }
  /** The file this is written in. */
  inline def here: String = ${ Lift.here }
  /** Where in its file this is written (an offset): the definition it is part of is found from it. */
  inline def at: Int = ${ Lift.at }

  /** The source text of each argument (used for what examples are given). */
  inline def sources(inline xs: Any*): List[String] = ${ Lift.sources('xs) }

/** A named function of the domain, defined once in Scala: it becomes a Lean
  * definition, can be called from other definitions and nodes, and runs as Scala.
  * Its Lean name is the name of the `val` it is assigned to.
  */
final class Def[F](val name: String, val lifted: Lifted[F]):
  def fn: F = lifted.value

object Def:
  /** The definitions given and every definition they use, however nested; each once, by name. */
  def closure(ds: Iterable[Def[?]]): List[Def[?]] =
    val out = scala.collection.mutable.LinkedHashMap.empty[String, Def[?]]
    def visit(d: Def[?]): Unit = if !out.contains(d.name) then { out(d.name) = d; d.lifted.defs.foreach(visit) }
    ds.foreach(visit)
    out.values.toList

/** A reason, a why or an exemption says something: a few words, not a placeholder. */
object Words:
  def tooFew(s: String): Boolean = s.trim.split("\\s+").count(_.exists(_.isLetter)) < 3

inline def define[F](inline f: F): Def[F] = ${ Lift.define('f) }

extension [A, R](d: Def[A => R]) def apply(a: A): R = d.fn(a)
extension [A, B, R](d: Def[(A, B) => R]) def apply(a: A, b: B): R = d.fn(a, b)
extension [A, B, C, R](d: Def[(A, B, C) => R]) def apply(a: A, b: B, c: C): R = d.fn(a, b, c)

/** Raised when specification-only logic is executed. */
final class NotExecutable(what: String) extends RuntimeException(s"$what cannot be executed")

/** For every value (specification only). */
def forall[A](p: A => Boolean): Boolean = throw NotExecutable("forall")
def forall[A, B](p: (A, B) => Boolean): Boolean = throw NotExecutable("forall")

/** For some value (specification only). */
def exists[A](p: A => Boolean): Boolean = throw NotExecutable("exists")
def exists[A, B](p: (A, B) => Boolean): Boolean = throw NotExecutable("exists")

extension (a: Boolean)
  /** Implication. */
  infix def ==>(b: => Boolean): Boolean = !a || b
