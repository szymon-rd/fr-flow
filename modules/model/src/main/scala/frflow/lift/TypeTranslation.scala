package frflow.lift

import frflow.*
import scala.collection.mutable
import scala.quoted.*

/** One translation's state and names, and the translation of Scala types to Lean types (declaring the
  * case classes and enums it meets). `Translator` adds the terms.
  */
private[lift] abstract class TypeTranslation(using val quotes: Quotes):
  import quotes.reflect.*

  // What the expansion has found so far, collected as the translation goes. A translator lives for one
  // macro expansion, so these buffers are never shared; threading them through every case of the
  // translation instead would double its code.
  protected val types = mutable.LinkedHashMap.empty[String, TypeDecl]
  private val inProgress = mutable.Set.empty[String]
  protected val deps = mutable.ListBuffer.empty[Term]
  protected val paramTerms = mutable.ListBuffer.empty[Term]
  protected val opaqueTerms = mutable.LinkedHashMap.empty[String, Term]
  protected val opaques = mutable.LinkedHashSet.empty[String]
  protected val paramRefs = mutable.LinkedHashMap.empty[String, String]
  /** Names bound locally (lambdas, quantifiers, patterns, lets): none may shadow a parameter, which
    * is a Lean variable of the same name.
    */
  private val binders = mutable.LinkedHashMap.empty[String, Position]
  private def bound(n: String, pos: Position): String = { binders.getOrElseUpdate(n, pos); n }
  /** Every local binder gets a Lean name of its own, used by no other binder in the expression: an
    * inner binder can then never capture an outer variable, whatever the Scala names (`x` and `x_1`,
    * a placeholder `_$1`, the same name in two scopes).
    */
  private val taken = mutable.Map.empty[String, AnyRef]
  protected def unique(owner: AnyRef, base: String, pos: Position, ok: String => Boolean = _ => true): String =
    // Nor a name a domain type starts with: `Share.mk` would read a field of a variable `Share`.
    val n = (Iterator(base) ++ Iterator.from(1).map(i => s"${base}_$i"))
      .filter(c => taken.get(c).forall(_ eq owner) && !paramRefs.contains(c) && !opaques.contains(c) &&
        !types.keys.exists(t => t == c || t.startsWith(c + ".")) && ok(c)).next() // (the candidates never end)
    taken(n) = owner
    bound(n, pos)
  protected def local(sym: Symbol, pos: Position): String = unique(sym, ident(sym.name), pos)
  protected def checkCapture(): Unit =
    binders.find((n, _) => paramRefs.contains(n) || opaques.contains(n)).foreach { (n, pos) =>
      fail(s"`$n` names both a parameter or opaque type and a local variable here; rename the local one", pos)
    }

  protected def fail(msg: String, pos: Position): Nothing = report.errorAndAbort(s"FrFlow: $msg", pos)
  protected def unsupported(t: Tree): Nothing =
    fail(s"not supported in a model: ${t.pos.sourceCode.filter(_.length <= 200).getOrElse(t.show)}${hint(t).fold("")(h => s"\n$h")}", t.pos)

  /** The usual rewrite into the subset, for the calls most often written outside it. */
  private def hint(t: Tree): Option[String] =
    def call(x: Tree): Option[(Term, String)] = x match
      case Apply(f, _)      => call(f)
      case TypeApply(f, _)  => call(f)
      case Inlined(_, _, b) => call(b)
      case Select(q, n)     => Some((q, n))
      case _                => None
    call(t).flatMap { (q, name) =>
      val qt = norm(q.tpe)
      def on(sym: Symbol) = qt.derivesFrom(sym)
      (name, on(ListSym), on(OptionSym), on(MapSym) || on(SetSym)) match
        case ("count", true, _, _)                    => Some("write it `xs.filter(p).length` (and `BigInt(xs.filter(p).length)` to compare it with a BigInt)")
        case ("sum" | "product", true, _, _)          => Some(s"write it with foldLeft: `xs.foldLeft(BigInt(${if name == "sum" then 0 else 1}))((a, x) => a ${if name == "sum" then "+" else "*"} x)`")
        case ("apply" | "last" | "head", true, _, _)  => Some("it throws on a short list: use `xs.drop(i).headOption`, or `headOption`")
        case ("toList", _, true, _)                   => Some("match on it: `o match { case Some(x) => List(x); case None => Nil }`")
        case ("map" | "flatMap" | "filter" | "fold" | "get" | "orElse", _, true, _) => Some("match on it: `o match { case Some(x) => ...; case None => ... }` (`get` throws on None)")
        case ("size" | "keys" | "values" | "toList" | "foreach" | "forall" | "exists" | "filter" | "map", _, _, true) =>
          Some("maps and sets are functions in Lean: what needs iterating them (sizes, every key) cannot be said; keep the data in a List")
        case _ => None
    }

  // ---------------------------------------------------------------------------
  // Types as values of the expansion
  // ---------------------------------------------------------------------------

  def leanType[T: Type]: Expr[LeanType] =
    val lean: String = tpe(TypeRepr.of[T], Position.ofMacroExpansion)
    '{ LeanType(${ Expr(lean) }, $typeList) }

  def typeList: Expr[List[TypeDecl]] =
    Expr.ofList(types.values.toList.map(d => '{ TypeDecl(${ Expr(d.name) }, ${ Expr(d.lean) }, ${ Expr(d.uses) }, ${ Expr(d.scala) }, ${ Expr(d.ctors) }) }))

  protected def strip(t: Term): Term = t match
    case Inlined(_, Nil, b) => strip(b)
    case Typed(e, _)        => strip(e)
    case Block(Nil, e)      => strip(e)
    case _                  => t

  protected def source(pos: Position): String =
    pos.sourceCode.filter(_.nonEmpty).orElse {
      scala.util.Try(java.nio.file.Files.readString(java.nio.file.Paths.get(pos.sourceFile.path)).substring(pos.start, pos.end)).toOption
    }.getOrElse("").trim

  // ---------------------------------------------------------------------------
  // Names
  // ---------------------------------------------------------------------------

  def ident(n: String): String = Names.ident(n)

  /** Owner chain without packages: `Wallet.total`, `Op.Deposit`. */
  def qualifiedName(sym: Symbol): String =
    def parts(s: Symbol): List[String] =
      if s.isNoSymbol || s.isPackageDef then Nil
      else
        val n = s.name.stripSuffix("$")
        if n.endsWith("$package") || n == "<root>" then parts(s.owner) else parts(s.owner) :+ ident(n)
    parts(sym).mkString(".")

  // ---------------------------------------------------------------------------
  // Types
  // ---------------------------------------------------------------------------

  protected lazy val ListSym = TypeRepr.of[List[Any]].typeSymbol
  protected lazy val OptionSym = TypeRepr.of[Option[Any]].typeSymbol
  protected lazy val MapSym = TypeRepr.of[Map[Any, Any]].typeSymbol
  protected lazy val SetSym = TypeRepr.of[Set[Any]].typeSymbol

  protected def norm(t: TypeRepr): TypeRepr = t.widenTermRefByName.widen.dealias

  protected def isLibrary(sym: Symbol) = sym.fullName.startsWith("scala.") || sym.fullName.startsWith("java.")

  protected def isAdt(sym: Symbol): Boolean =
    sym.isClassDef && !isLibrary(sym) && !sym.flags.is(Flags.Module) &&
      ((sym.flags.is(Flags.Case) && !sym.flags.is(Flags.Enum)) || (sym.flags.is(Flags.Enum) && !sym.flags.is(Flags.Case)))

  /** Whether a value of the type holds a bounded integer (Int or Long), however deep. */
  protected def bounded(t0: TypeRepr, seen: Set[Symbol] = Set.empty): Boolean =
    val t = norm(t0)
    if t =:= TypeRepr.of[Int] || t =:= TypeRepr.of[Long] then true
    else if isAdt(t.typeSymbol) && !seen(t.typeSymbol) then
      val sym = t.typeSymbol
      val cases = if sym.flags.is(Flags.Enum) then sym.children.filter(_.isClassDef) else List(sym)
      cases.exists(c => c.caseFields.exists(f => bounded(c.typeRef.memberType(f), seen + sym)))
    else t.typeArgs.exists(bounded(_, seen))

  protected def isInt(t: TypeRepr) = norm(t) =:= TypeRepr.of[Int] || norm(t) =:= TypeRepr.of[Long] || isBig(t)
  protected def isBig(t: TypeRepr) = norm(t) =:= TypeRepr.of[BigInt]
  /** Scala's `Int` and `Long` wrap around; Lean's integers do not, nor does `BigInt`. */
  protected def exact(qt: TypeRepr, op: String, pos: Position): Unit =
    if !isBig(qt) then fail(s"`$op` on Int or Long can overflow in Scala, not in Lean: use BigInt for arithmetic", pos)
  /** A divisor known not to be zero: Lean divides by zero to 0, Scala throws. */
  protected def nonZero(t: Term): Boolean = strip(t) match
    case Literal(c) => c.value match
      case i: Int  => i != 0
      case l: Long => l != 0
      case _       => false
    case Apply(f, List(x)) if Set("int2bigInt", "long2bigInt", "apply")(f.symbol.name) => nonZero(x)
    case _ => false

  def tpe(t0: TypeRepr, pos: Position): String =
    val t = norm(t0)
    def arg(cls: Symbol) = tpe(t.baseType(cls).typeArgs.head, pos)
    if t =:= TypeRepr.of[Nothing] then fail("cannot infer the type here; add a type ascription", pos)
    else if isOpaque(t) then
      val n = opaqueName(t, pos)
      opaques += n
      t match
        case TypeRef(prefix: TermRef, _) if !opaqueTerms.contains(n) => opaqueTerms(n) = Ref.term(prefix)
        case _ => ()
      n
    else if t =:= TypeRepr.of[Boolean] then "Prop"
    else if isInt(t) then "Int"
    else if t =:= TypeRepr.of[String] then "String"
    else if t =:= TypeRepr.of[Unit] then "Unit"
    // A map is the function from its keys to what each is bound to; a set, its membership.
    else if t.derivesFrom(MapSym) then
      val List(k, v) = t.baseType(MapSym).typeArgs
      s"(${tpe(k, pos)} → Option ${tpe(v, pos)})"
    else if t.derivesFrom(SetSym) then s"(${arg(SetSym)} → Prop)"
    else if t.derivesFrom(ListSym) then s"(List ${arg(ListSym)})"
    else if t.derivesFrom(OptionSym) then s"(Option ${arg(OptionSym)})"
    else if defn.isTupleClass(t.typeSymbol) then t.typeArgs.map(tpe(_, pos)).mkString("(", " × ", ")")
    else if t.isFunctionType then "(" + t.typeArgs.map(tpe(_, pos)).mkString(" → ") + ")"
    else if isAdt(t.typeSymbol) && t.typeArgs.isEmpty then declare(t.typeSymbol, pos)
    else fail(s"type ${t.show} is not supported; model the domain with case classes and enums", pos)

  /** `User.T` for `val User = Opaque("User")`. */
  private def isOpaque(t: TypeRepr): Boolean = t match
    case TypeRef(_, "T") => t.typeSymbol.owner.fullName == "frflow.Opaque"
    case _               => false

  private def opaqueName(t: TypeRepr, pos: Position): String = t match
    case TypeRef(prefix: TermRef, _) => ident(prefix.termSymbol.name)
    case _                           => fail(s"refer to an opaque type through its val, as in `User.T`", pos)

  private def adtRefs(t: TypeRepr): List[Symbol] =
    val n = norm(t)
    (if isAdt(n.typeSymbol) then List(n.typeSymbol) else Nil) ++ n.typeArgs.flatMap(adtRefs)

  private def doc(sym: Symbol): String =
    sym.docstring.map(_.stripPrefix("/**").stripSuffix("*/").linesIterator.map(_.trim.stripPrefix("*").trim)
      .takeWhile(l => !l.startsWith("@")).mkString(" ").trim).filter(_.nonEmpty)
      .fold("")(d => s"/-- ${d.replace("-/", "- /")} -/\n")

  /** Declares a case class or enum and returns its Lean name. */
  protected def declare(sym: Symbol, pos: Position): String =
    val name = qualifiedName(sym)
    if !types.contains(name) && !inProgress(name) then
      // Lean equality is structural; a class that redefines equality, itself or through a trait,
      // would mean something else at run time.
      val standard = Set("scala.Any", "java.lang.Object", "scala.AnyRef", "scala.Product", "scala.Equals", "scala.reflect.Enum")
      // (Each case of an enum too: a case may extend a trait of its own.)
      (sym :: (if sym.flags.is(Flags.Enum) then sym.children else Nil)).foreach { c =>
        c.typeRef.baseClasses.filterNot(b => standard(b.fullName) || b == sym && c != sym).foreach { b =>
          List("equals", "hashCode", "canEqual").flatMap(b.declaredMethod).filterNot(_.flags.is(Flags.Synthetic)).foreach(m =>
            fail(s"${c.name} redefines ${m.name} (in ${b.name}): domain types must keep structural equality", pos))
        }
      }
      inProgress += name
      def field(cls: Symbol, f: Symbol): (String, TypeRepr) =
        val t = cls.typeRef.memberType(f)
        // Scala compares a function field by reference, Lean by its values: they would disagree.
        if t.widen.dealias.isFunctionType then fail(s"${cls.name}.${f.name} is a function: a domain type's fields must be data", pos)
        (ident(f.name), t)
      // The Scala shape of the type, as written (Scala's names, not Lean's): what a decision depends on.
      def shape(fs: List[(String, TypeRepr)]) = if fs.isEmpty then "" else fs.map((n, t) => s"$n: ${t.show(using Printer.TypeReprShortCode)}").mkString("(", ", ", ")")
      val scala =
        if sym.flags.is(Flags.Enum) then
          s"enum ${sym.name}: " + sym.children.map(c => "case " + c.name + shape(if c.isClassDef then c.caseFields.map(f => f.name -> field(c, f)._2) else Nil)).mkString(", ")
        else s"case class ${sym.name}${shape(sym.caseFields.map(f => f.name -> field(sym, f)._2))}"
      val ctors: List[(String, List[(String, TypeRepr)])] =
        if sym.flags.is(Flags.Enum) then sym.children.map(c => ident(c.name) -> (if c.isClassDef then c.caseFields.map(field(c, _)) else Nil))
        else List("mk" -> sym.caseFields.map(field(sym, _)))
      val leanCtors = ctors.map((c, fs) => c -> fs.map((n, t) => n -> tpe(t, pos)))
      val lean =
        if sym.flags.is(Flags.Enum) then
          s"${doc(sym)}inductive $name where\n" + leanCtors.map((c, fs) => s"  | $c${fs.map((n, t) => s" ($n : $t)").mkString}").mkString("\n")
        else
          val fs = leanCtors.head._2
          s"${doc(sym)}structure $name" + (if fs.isEmpty then "" else " where\n" + fs.map((n, t) => s"  $n : $t").mkString("\n"))
      val refs = ctors.flatMap(_._2.map(_._2))
      val uses = refs.flatMap(adtRefs).map(qualifiedName).distinct.filterNot(_ == name)
      types(name) = TypeDecl(name, lean, uses, scala, leanCtors)
      inProgress -= name
    name
