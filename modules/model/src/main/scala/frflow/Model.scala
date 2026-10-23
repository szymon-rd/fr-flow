package frflow

import frflow.protocol.Walk

/** A domain type, open until a definition fixes it: `val User = Opaque("User", "a person with an account")`, used as `User.T`. */
final class Opaque(val name: String, val means: String):
  type T
  given leanType: LeanType[T] = LeanType.of(Shape.Opq(this))
  def :=(t: LeanType[?]): Subst = Subst(name, this, isType = true, Some(t), None)

/** A domain term, open until a definition fixes it: a fact of the world, or an operation some contract is about.
  * It is a term: `grants.contains(g)`, `sessions(t)`. Plain code reads its value in force with `value`. One that only
  * plain code reads (a database handle) needs no Lean type.
  */
final class Param[A](val name: String, val means: String)(using t: LeanType[A] = LeanType.unknown[A]) extends Term[A](null, t):
  override private[frflow] def termTree: Tree = Tree.Ref(this)
  def value: A = Bindings.get(this)
  inline def :=(inline v: Term[A]): Subst = Subst.term(this, Lifted.term(() => v, Source.text(v)))
  inline def :=[X, R](inline f: Term[X] => Term[R])(using x: LeanType[X]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x), Source.text(f)))
  inline def :=[X, Y, R](inline f: (Term[X], Term[Y]) => Term[R])(using x: LeanType[X], y: LeanType[Y]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y), Source.text(f)))
  inline def :=[X, Y, Z, R](inline f: (Term[X], Term[Y], Term[Z]) => Term[R])(using x: LeanType[X], y: LeanType[Y], z: LeanType[Z]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y, z), Source.text(f)))
  /** Evaluated on every use. */
  def bind(v: => A): Binding = Binding(this, () => v)
  /** `bind(table.get)`, with the table given to Lean too, so the examples are evaluated there. */
  def bindTable[K, V](table: Map[K, V])(using A =:= (K => Option[V])): Binding = Binding(this, () => table.get, Some(table))
  override def toString: String = name

// A parameter called in a model is a term; plain code calls the value in force: `sessions.value(t)`.
extension [A, R](p: Param[A => R])
  def apply(a: Term[A]): Term[R] = Term.applied(p, a)
extension [A, B, R](p: Param[(A, B) => R])
  def apply(a: Term[A], b: Term[B]): Term[R] = Term.applied(p, a, b)
extension [A, B, C, R](p: Param[(A, B, C) => R])
  def apply(a: Term[A], b: Term[B], c: Term[C]): Term[R] = Term.applied(p, a, b, c)
extension [A, B, C, D, R](p: Param[(A, B, C, D) => R])
  def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D]): Term[R] = Term.applied(p, a, b, c, e)
extension [A, B, C, D, E, R](p: Param[(A, B, C, D, E) => R])
  def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E]): Term[R] = Term.applied(p, a, b, c, e, f)

/** A definition of one term: a type (`User := of[UserId]`) or a function of the domain (`authorized := (u, p) => …`). */
final class Subst private[frflow] (val name: String, val target: AnyRef, val isType: Boolean, typeOf: Option[LeanType[?]],
    val term: Option[Lifted[?]]):
  private lazy val walked = typeOf.map(Types.walk)
  def lean: String = walked.fold(term.fold("")(_.lean))(_.lean)
  def types: List[TypeDecl] = walked.fold(term.fold(Nil)(_.types))(_.types)
  def param: Option[Param[?]] = target match { case p: Param[?] => Some(p); case _ => None }
object Subst:
  def term(p: Param[?], l: Lifted[?]): Subst = Subst(p.name, p, isType = false, None, Some(l))

/** The Lean translation of a Scala type: `User := of[UserId]`. */
def of[T](using t: LeanType[T]): LeanType[T] = t

final case class Binding(param: Param[?], value: () => Any, table: Option[Map[?, ?]] = None)

final case class TypeDecl(name: String, lean: String, uses: List[String], scala: String = "", ctors: List[(String, List[(String, String)])] = Nil):
  /** Without its doc comment: a file compiled on its own may not see the comment. */
  def body: String = if lean.startsWith("/--") then lean.drop(lean.indexOf("-/\n") + 3) else lean

/** A lambda over terms (or a term), with its Lean and its Scala: built when first used, after every val of the model
  * is set, so a model may name a `define` declared below it.
  */
final class Lifted[+F] private[frflow] (build: () => (List[Binder], Term[?]), private[frflow] val fn: AnyRef | Null, val source: String,
    asValue: Boolean = false, runs: Lifted[?] | Null = null):
  private lazy val built = build()
  private lazy val printed: Printed = LeanPrinter().print(built._1, built._2.termTree, built._2.termType)
  private lazy val compiled: AnyRef = Eval.function(built._1, built._2.termTree)
  /** The Scala function; a term defined as a value (`onShelf := shelf.length`), its value under the bindings in force. */
  def value: F = (if runs != null then runs.value else if asValue then compiled.asInstanceOf[() => Any]() else compiled).asInstanceOf[F]
  /** The same Lean, run by another's Scala: how a test injects a translation bug. */
  private[frflow] def runningAs(other: Lifted[?]): Lifted[F] = Lifted(build, fn, source, asValue, other)
  def params: List[(String, String)] = printed.params
  def result: String = printed.result
  def body: String = printed.body
  def types: List[TypeDecl] = printed.types
  def opaques: List[String] = printed.opaques.map(o => Names.ident(o.name))
  def paramRefs: List[(String, String)] = printed.paramRefs
  def defs: List[Def[?]] = printed.defs
  def paramObjects: List[Param[?]] = printed.paramObjects
  def opaqueObjects: List[Opaque] = printed.opaques
  def lean: String = if params.isEmpty then body else s"fun ${params.map((n, t) => s"($n : $t)").mkString(" ")} => $body"
  def leanType: String = (params.map(_._2) :+ result).mkString(" → ")

object Lifted:
  /** A term, built when first used. */
  @scala.annotation.publicInBinary private[frflow] def thunk(t: () => Term[?], source: String): Lifted[() => Any] = Lifted(() => (Nil, t()), null, source)
  /** A term defined as a value. */
  @scala.annotation.publicInBinary private[frflow] def term(t: () => Term[?], source: String): Lifted[Any] = Lifted(() => (Nil, t()), null, source, asValue = true)
  /** A lambda over terms of these types. */
  @scala.annotation.publicInBinary private[frflow] def lambda[F](f: AnyRef, types: List[LeanType[?]], source: String): Lifted[F] =
    Lifted(() => { val bs = Lambda.binders(f, types); (bs, Lambda.body(f, bs)) }, f, source)

/** A function of the domain, defined once with terms: a Lean definition named as its `val`, and run as Scala. */
final class Def[F] @scala.annotation.publicInBinary private[frflow] (val lifted: Lifted[F], private[frflow] val resultType: LeanType[?],
    named: Option[String] = None):
  lazy val name: String = named.orElse(Lambdas.valName(this, lifted.fn.nn))
    .getOrElse(throw IllegalStateException("FrFlow: a `define` must be assigned to a top-level val, or a val of an object"))
  def fn: F = lifted.value
  override def toString: String = name
object Def:
  def closure(ds: Iterable[Def[?]]): List[Def[?]] = Walk.preorder(ds.toList, _.name)(_.lifted.defs)

/** `define { (b: Term[Book]) => b.pages >= 100 }`: named in Lean as the val it is assigned to. */
inline def define[A, R](inline f: Term[A] => Term[R])(using a: LeanType[A], r: LeanType[R]): Def[A => R] =
  Def(Lifted.lambda(f, List(a), Source.text(f)), r)
inline def define[A, B, R](inline f: (Term[A], Term[B]) => Term[R])(using a: LeanType[A], b: LeanType[B], r: LeanType[R]): Def[(A, B) => R] =
  Def(Lifted.lambda(f, List(a, b), Source.text(f)), r)
inline def define[A, B, C, R](inline f: (Term[A], Term[B], Term[C]) => Term[R])(using a: LeanType[A], b: LeanType[B], c: LeanType[C],
    r: LeanType[R]): Def[(A, B, C) => R] =
  Def(Lifted.lambda(f, List(a, b, c), Source.text(f)), r)
inline def define[A, B, C, D, R](inline f: (Term[A], Term[B], Term[C], Term[D]) => Term[R])(using a: LeanType[A], b: LeanType[B],
    c: LeanType[C], d: LeanType[D], r: LeanType[R]): Def[(A, B, C, D) => R] =
  Def(Lifted.lambda(f, List(a, b, c, d), Source.text(f)), r)
inline def define[A, B, C, D, E, R](inline f: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[R])(using a: LeanType[A], b: LeanType[B],
    c: LeanType[C], d: LeanType[D], e: LeanType[E], r: LeanType[R]): Def[(A, B, C, D, E) => R] =
  Def(Lifted.lambda(f, List(a, b, c, d, e), Source.text(f)), r)

private def called[R](d: Def[?], args: Term[?]*): Term[R] =
  Term(Tree.Call(d, args.toList.map(_.termTree)), d.resultType.asInstanceOf[LeanType[R]])

// A define called in a model is a term; plain code runs it with `fn`: `admitted.fn(token, path)`.
extension [A, R](d: Def[A => R])
  def apply(a: Term[A]): Term[R] = called(d, a)
extension [A, B, R](d: Def[(A, B) => R])
  def apply(a: Term[A], b: Term[B]): Term[R] = called(d, a, b)
extension [A, B, C, R](d: Def[(A, B, C) => R])
  def apply(a: Term[A], b: Term[B], c: Term[C]): Term[R] = called(d, a, b, c)
extension [A, B, C, D, R](d: Def[(A, B, C, D) => R])
  def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D]): Term[R] = called(d, a, b, c, e)
extension [A, B, C, D, E, R](d: Def[(A, B, C, D, E) => R])
  def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E]): Term[R] = called(d, a, b, c, e, f)

/** `forall` and `exists` say something of every value: Scala cannot compute them, so running one throws this. */
final class NotExecutable(what: String) extends RuntimeException(s"$what cannot be executed")

extension (a: Boolean) infix def ==>(b: => Boolean): Boolean = !a || b

/** Lean names and literals for Scala ones: shared by the Lean printer and the Lean generator. */
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
