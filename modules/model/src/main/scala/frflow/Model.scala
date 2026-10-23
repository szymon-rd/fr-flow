package frflow

import frflow.lift.Lift
import frflow.protocol.Walk

/** A domain type, open until a definition fixes it: `val User = Opaque("User", "a person with an account")`, used as `User.T`. */
final class Opaque(val name: String, val means: String):
  type T
  def :=(t: LeanType): Subst = Subst(name, t.lean, t.types, None, isType = true, this)

/** A domain term, open until a definition fixes it: a fact of the world, or an operation some contract is about. */
final class Param[A](val name: String, val means: String):
  def value: A = Bindings.get(this)
  inline def :=[B](inline v: B): Subst = Subst.param(this, Lifted(v))
  /** Evaluated on every use. */
  def bind(v: => A): Binding = Binding(this, () => v)
  /** `bind(table.get)`, with the table given to Lean too, so the examples are evaluated there. */
  def bindTable[K, V](table: Map[K, V])(using A =:= (K => Option[V])): Binding = Binding(this, () => table.get, Some(table))

extension [A, R](p: Param[A => R]) def apply(a: A): R = p.value(a)
extension [A, B, R](p: Param[(A, B) => R]) def apply(a: A, b: B): R = p.value(a, b)
extension [A, B, C, R](p: Param[(A, B, C) => R]) def apply(a: A, b: B, c: C): R = p.value(a, b, c)
extension [A, B, C, D, R](p: Param[(A, B, C, D) => R]) def apply(a: A, b: B, c: C, e: D): R = p.value(a, b, c, e)
extension [A, B, C, D, E, R](p: Param[(A, B, C, D, E) => R]) def apply(a: A, b: B, c: C, e: D, f: E): R = p.value(a, b, c, e, f)

final case class Subst(name: String, lean: String, types: List[TypeDecl], term: Option[Lifted[?]], isType: Boolean, target: AnyRef):
  def param: Option[Param[?]] = target match { case p: Param[?] => Some(p); case _ => None }
object Subst:
  def param(p: Param[?], l: Lifted[?]): Subst = Subst(p.name, l.lean, l.types, Some(l), isType = false, p)

final case class LeanType(lean: String, types: List[TypeDecl])

/** The Lean translation of a Scala type: `User := of[UserId]`. */
inline def of[T]: LeanType = ${ Lift.leanType[T] }

final case class Binding(param: Param[?], value: () => Any, table: Option[Map[?, ?]] = None)

final case class TypeDecl(name: String, lean: String, uses: List[String], scala: String = "", ctors: List[(String, List[(String, String)])] = Nil):
  /** Without its doc comment: a file compiled on its own may not see the comment. */
  def body: String = if lean.startsWith("/--") then lean.drop(lean.indexOf("-/\n") + 3) else lean

/** A Scala lambda or value with its Lean translation; the value is evaluated on each use, under the bindings in force. */
final class Lifted[+F](valueThunk: () => F, val params: List[(String, String)], val result: String, val body: String,
    val source: String, val types: List[TypeDecl], val opaques: List[String], val paramRefs: List[(String, String)],
    defsThunk: () => List[Def[?]], paramsThunk: () => List[Param[?]], opaquesThunk: () => List[Opaque] = () => Nil):
  def value: F = valueThunk()
  def defs: List[Def[?]] = defsThunk()
  def paramObjects: List[Param[?]] = paramsThunk()
  def opaqueObjects: List[Opaque] = opaquesThunk()
  def lean: String = if params.isEmpty then body else s"fun ${params.map((n, t) => s"($n : $t)").mkString(" ")} => $body"
  def leanType: String = (params.map(_._2) :+ result).mkString(" → ")
object Lifted:
  /** Translates a Scala lambda over the domain. Unsupported Scala is a compile error. */
  inline def apply[F](inline f: F): Lifted[F] = ${ Lift.lifted('f) }
  inline def sourceFiles(inline x: Any): List[String] = ${ Lift.sourceFiles('x) }
  inline def here: String = ${ Lift.here }
  inline def at: Int = ${ Lift.at }
  inline def sources(inline xs: Any*): List[String] = ${ Lift.sources('xs) }

/** A function of the domain, defined once in Scala: a Lean definition named as its `val`, and run as Scala. */
final class Def[F](val name: String, val lifted: Lifted[F]):
  def fn: F = lifted.value
object Def:
  def closure(ds: Iterable[Def[?]]): List[Def[?]] = Walk.preorder(ds.toList, _.name)(_.lifted.defs)

inline def define[F](inline f: F): Def[F] = ${ Lift.define('f) }

extension [A, R](d: Def[A => R]) def apply(a: A): R = d.fn(a)
extension [A, B, R](d: Def[(A, B) => R]) def apply(a: A, b: B): R = d.fn(a, b)
extension [A, B, C, R](d: Def[(A, B, C) => R]) def apply(a: A, b: B, c: C): R = d.fn(a, b, c)
extension [A, B, C, D, R](d: Def[(A, B, C, D) => R]) def apply(a: A, b: B, c: C, e: D): R = d.fn(a, b, c, e)
extension [A, B, C, D, E, R](d: Def[(A, B, C, D, E) => R]) def apply(a: A, b: B, c: C, e: D, f: E): R = d.fn(a, b, c, e, f)

/** `forall` and `exists` are Booleans to Scala: the only way they can say they cannot be computed is to throw. */
final class NotExecutable(what: String) extends RuntimeException(s"$what cannot be executed")

/** For every value (specification only). */
def forall[A](p: A => Boolean): Boolean = throw NotExecutable("forall")
def forall[A, B](p: (A, B) => Boolean): Boolean = throw NotExecutable("forall")
/** For some value (specification only). */
def exists[A](p: A => Boolean): Boolean = throw NotExecutable("exists")
def exists[A, B](p: (A, B) => Boolean): Boolean = throw NotExecutable("exists")

extension (a: Boolean) infix def ==>(b: => Boolean): Boolean = !a || b

/** Lean names and literals for Scala ones: shared by the macro and the Lean generator. */
private[frflow] object Names:
  private val Keywords = Set("at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "then", "with",
    "from", "show", "where", "open", "namespace", "section", "def", "theorem", "structure", "inductive", "instance", "import",
    "forall", "exists", "Type", "Prop", "Sort", "this", "deriving", "mut", "return", "for", "try", "catch", "matches", "variable",
    "universe", "axiom", "example", "abbrev", "class", "extends", "local", "private", "protected", "partial", "unsafe", "macro",
    "syntax", "notation", "calc", "suffices", "obtain", "using", "λ", "nomatch", "nofun", "termination_by", "decreasing_by",
    "mutual", "opaque", "noncomputable", "until", "unless", "repeat", "while", "break", "continue", "attribute", "export",
    "hiding", "renaming", "omit", "include", "elab", "init")

  /** Lean names the generated code uses or the prelude defines: a Scala name equal to one is renamed, so it cannot capture them. */
  val Prelude: Set[String] = Set(
    "some", "none", "True", "False", "true", "false", "max", "min", "decide", "List", "Option", "Int", "Nat", "Bool",
    "String", "Prod", "Exists", "Eq", "Ne", "Not", "And", "Or", "Iff", "id", "ite", "dite", "Classical", "Unit", "Function",
    "not", "and", "or", "xor", "cond", "Decidable", "propext", "funext", "rfl", "trivial", "absurd", "sorry", "FrFlow")

  def ident(n: String): String =
    val s = n.replace('$', '_')
    val t = if s.startsWith("__") then "x" + s.drop(1) else s
    if Keywords(t) then s"«$t»" else if Prelude(t) then t + "_" else t

  /** The call markers ⟦ ⟧ are escaped, so a string can never be read as a call. */
  def string(s: String): String = "\"" + s.flatMap {
    case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case '\t' => "\\t"; case '\r' => "\\r"
    case '⟦' => "\\u27E6"; case '⟧' => "\\u27E7"
    case ch if ch < ' ' => f"\\x${ch.toInt}%02x"
    case ch => ch.toString
  } + "\""
