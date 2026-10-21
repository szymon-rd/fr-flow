package frflow.lift

import frflow.ir.*
import scala.collection.mutable
import scala.quoted.{Expr as QExpr, Quotes, Type as QType}

/** Compile-time translation of Scala code to FrFlow IR.
  *
  * The translated subset:
  *   - case classes (Lean structures) and Scala 3 enums (Lean inductive types);
  *   - methods of those types and functions and values in objects, read from
  *     their definitions (the using module must compile with `-Yretain-trees`);
  *   - lambdas, `val`s, `if`, `match` on constructors, literals, tuples;
  *   - `Boolean`, `Int`/`Long`/`BigInt` (as mathematical integers), `String`;
  *   - immutable `List`, `Set`, `Map` and `Option` with the operations listed in
  *     `Builtins`;
  *   - `forall`, `exists` and `==>` from `frflow.dsl` (specification only).
  *
  * Anything else is a compile error at the offending position.
  */
object LiftMacro:

  def liftCode[F: QType](f: QExpr[F])(using Quotes): QExpr[Code[F]] =
    val res = Translator().liftExpr(f)
    val chunks = QExpr(IrCodec.encodeChunks(res))
    '{ new Code[F](() => $f, $chunks) }

  def schema[T: QType](using Quotes): QExpr[Schema[T]] =
    val res = Translator().liftQType[T]
    val chunks = QExpr(IrCodec.encodeChunks(res))
    '{ new Schema[T]($chunks) }

private final class Translator(using val quotes: Quotes):
  import quotes.reflect.*

  private val adts = mutable.LinkedHashMap.empty[String, AdtDef]
  private val funs = mutable.LinkedHashMap.empty[String, FunDef]
  private val adtsInProgress = mutable.Set.empty[String]
  private val funsInProgress = mutable.Set.empty[String]

  private def defs: Defs = Defs(adts.toMap, funs.toMap)

  private def fail(msg: String, pos: Position): Nothing = report.errorAndAbort(s"FrFlow: $msg", pos)

  // ---------------------------------------------------------------------------
  // Entry points
  // ---------------------------------------------------------------------------

  def liftExpr(e: QExpr[?]): LiftResult = liftTerm(e.asTerm)

  def liftQType[T: QType]: LiftResult = liftType(TypeRepr.of[T], Position.ofMacroExpansion)

  def liftTerm(t: Term): LiftResult =
    val e = term(t, Env.empty)
    val ft = t.tpe.widen.dealias
    val (params, body, result) = e match
      case Expr.Lam(ps, b) =>
        val res = if ft.isFunctionType then ft.typeArgs.last else ft
        (ps, b, tpe(res, t.pos))
      case other => (Nil, other, tpe(ft, t.pos))
    val src = innermost(t)
    val lifted = Lifted(params, result, body, sourceText(src.pos), position(src.pos))
    LiftResult(Some(lifted), Type.Fun(params.map(_.tpe), result), defs)

  def liftType(t: TypeRepr, pos: Position): LiftResult =
    val ty = tpe(t, pos)
    LiftResult(None, ty, defs)

  /** The user's expression inside the wrappers that inlining adds; its position is in the user's file. */
  private def innermost(t: Term): Term = t match
    case Inlined(_, Nil, b) => innermost(b)
    case Typed(e, _)        => innermost(e)
    case _                  => t

  private def position(pos: Position): String = s"${pos.sourceFile.name}:${pos.startLine + 1}"

  // ---------------------------------------------------------------------------
  // Names, documentation and sources
  // ---------------------------------------------------------------------------

  private val libraryPrefixes = List("scala.", "java.", "frflow.dsl.", "frflow.lift.", "frflow.ir.", "frflow.runtime.")
  private def isLibrary(sym: Symbol): Boolean = libraryPrefixes.exists(sym.fullName.startsWith)

  private def cleanName(n: String): String = n.stripSuffix("$")

  /** Scala names with `$` (synthetic and placeholder parameters) as Lean identifiers: `x$1` → `x_1`, `_$1` → `x_1`. */
  def sanitize(n: String): String =
    val s = n.replace('$', '_')
    if s.startsWith("__") then "x" + s.drop(1) else s

  /** Lean name of a symbol: its owner chain without packages. */
  def leanName(sym: Symbol): String =
    def parts(s: Symbol): List[String] =
      if s.isNoSymbol || s.isPackageDef then Nil
      else
        val n = cleanName(s.name)
        val rest = parts(s.owner)
        if n.endsWith("$package") || n.isEmpty || n == "<root>" then rest else rest :+ n
    parts(sym).mkString(".")

  private def cleanDoc(raw: String): String =
    raw.stripPrefix("/**").stripSuffix("*/").linesIterator
      .map(_.trim.stripPrefix("*").trim)
      .takeWhile(l => !l.startsWith("@"))
      .mkString(" ").replaceAll("""\s+""", " ").trim

  private def doc(sym: Symbol): String = sym.docstring.map(cleanDoc).getOrElse("")

  /** Documentation of a case class field, from `@param` in the class comment. */
  private def paramDoc(cls: Symbol, field: String): String =
    val raw = cls.docstring.getOrElse("").trim.stripPrefix("/**").stripSuffix("*/")
    val lines = raw.linesIterator.map(_.trim.stripPrefix("*").trim).toList
    val start = lines.indexWhere(l => l.startsWith(s"@param $field ") || l == s"@param $field")
    if start < 0 then ""
    else
      val first = lines(start).stripPrefix(s"@param $field").trim
      val rest = lines.drop(start + 1).takeWhile(l => !l.startsWith("@"))
      (first :: rest).mkString(" ").replaceAll("""\s+""", " ").trim

  private def source(sym: Symbol): String =
    try sourceText(sym.tree.pos)
    catch case _: Throwable => ""

  /** Source text of a position; read from the file when the compiler did not load it (definitions from TASTy). */
  private def sourceText(pos: Position): String =
    pos.sourceCode.filter(_.nonEmpty).orElse {
      try
        Some(java.nio.file.Paths.get(pos.sourceFile.path)).filter(java.nio.file.Files.isRegularFile(_)).map { p =>
          val text = java.nio.file.Files.readString(p)
          if pos.end <= text.length && pos.start <= pos.end then text.substring(pos.start, pos.end) else ""
        }
      catch case _: Throwable => None
    }.getOrElse("").trim

  // ---------------------------------------------------------------------------
  // Types
  // ---------------------------------------------------------------------------

  private lazy val ListSym = TypeRepr.of[List[Any]].typeSymbol
  private lazy val SetSym = TypeRepr.of[Set[Any]].typeSymbol
  private lazy val MapSym = TypeRepr.of[Map[Any, Any]].typeSymbol
  private lazy val OptionSym = TypeRepr.of[Option[Any]].typeSymbol

  private def norm(t: TypeRepr): TypeRepr = t.widenTermRefByName.widen.dealias

  private def isInt(t: TypeRepr): Boolean =
    val n = norm(t)
    n =:= TypeRepr.of[Int] || n =:= TypeRepr.of[Long] || n =:= TypeRepr.of[BigInt]

  private def isAdtClass(sym: Symbol): Boolean =
    sym.isClassDef && !isLibrary(sym) && (
      (sym.flags.is(Flags.Case) && !sym.flags.is(Flags.Enum) && !sym.flags.is(Flags.Module)) ||
        (sym.flags.is(Flags.Enum) && !sym.flags.is(Flags.Case))
    )

  private def typeArg(t: TypeRepr, cls: Symbol, i: Int, pos: Position): Type =
    tpe(t.baseType(cls).typeArgs(i), pos)

  def tpe(t0: TypeRepr, pos: Position): Type =
    val t = norm(t0)
    if t =:= TypeRepr.of[Boolean] then Type.Bool
    else if isInt(t) then Type.Int
    else if t =:= TypeRepr.of[String] then Type.Str
    else if t =:= TypeRepr.of[Unit] then Type.Unit
    else if t =:= TypeRepr.of[Nothing] then fail("the type Nothing cannot be translated; add a type ascription", pos)
    else if t.derivesFrom(ListSym) then Type.ListOf(typeArg(t, ListSym, 0, pos))
    else if t.derivesFrom(SetSym) then Type.SetOf(typeArg(t, SetSym, 0, pos))
    else if t.derivesFrom(MapSym) then Type.MapOf(typeArg(t, MapSym, 0, pos), typeArg(t, MapSym, 1, pos))
    else if t.derivesFrom(OptionSym) then Type.OptionOf(typeArg(t, OptionSym, 0, pos))
    else if t.isFunctionType then
      val as = t.typeArgs
      Type.Fun(as.init.map(tpe(_, pos)), tpe(as.last, pos))
    else if defn.isTupleClass(t.typeSymbol) then Type.TupleOf(t.typeArgs.map(tpe(_, pos)))
    else
      val sym = t.typeSymbol
      if isAdtClass(sym) then
        if t.typeArgs.nonEmpty then fail(s"generic ADTs are not supported: ${t.show}", pos)
        Type.Named(registerAdt(sym, pos))
      else if sym.flags.is(Flags.Case) && sym.flags.is(Flags.Enum) then
        fail(s"use the enum type instead of the enum case type ${t.show}", pos)
      else if sym.flags.is(Flags.Sealed) || sym.flags.is(Flags.Trait) then
        fail(s"${t.show}: sealed hierarchies are not supported; model alternatives as a Scala 3 enum", pos)
      else fail(s"unsupported type ${t.show}; use case classes, enums, Boolean, Int, Long, BigInt, String, List, Set, Map, Option, tuples or functions", pos)

  /** Whether `tpe` would succeed, without reporting errors. */
  private def canTranslate(t0: TypeRepr): Boolean =
    val t = norm(t0)
    def base(cls: Symbol): List[TypeRepr] = t.baseType(cls).typeArgs
    if t =:= TypeRepr.of[Nothing] then false
    else if t =:= TypeRepr.of[Boolean] || isInt(t) || t =:= TypeRepr.of[String] || t =:= TypeRepr.of[Unit] then true
    else if t.derivesFrom(ListSym) then base(ListSym).forall(canTranslate)
    else if t.derivesFrom(SetSym) then base(SetSym).forall(canTranslate)
    else if t.derivesFrom(MapSym) then base(MapSym).forall(canTranslate)
    else if t.derivesFrom(OptionSym) then base(OptionSym).forall(canTranslate)
    else if t.isFunctionType || defn.isTupleClass(t.typeSymbol) then t.typeArgs.forall(canTranslate)
    else isAdtClass(t.typeSymbol) && t.typeArgs.isEmpty

  /** Type annotation for empty collections, when the type is known. */
  private def tryTpe(t: TypeRepr): Option[Type] =
    if canTranslate(t) then Some(tpe(t, Position.ofMacroExpansion)) else None

  /** Lean name to Scala name, to reject two Scala definitions with the same Lean name. */
  private val owners = mutable.Map.empty[String, String]

  private def claim(name: String, sym: Symbol, pos: Position): Unit =
    owners.get(name) match
      case Some(other) if other != sym.fullName =>
        fail(s"$other and ${sym.fullName} both translate to the Lean name $name; rename one of them", pos)
      case _ => owners(name) = sym.fullName

  private def registerAdt(sym: Symbol, pos: Position): String =
    val name = leanName(sym)
    claim(name, sym, pos)
    if !adts.contains(name) && !adtsInProgress(name) then
      adtsInProgress += name
      val shape =
        if sym.flags.is(Flags.Enum) then
          val cases = sym.children
          if cases.isEmpty then fail(s"enum ${sym.name} has no cases", pos)
          AdtShape.Sum(cases.map { c =>
            val fields = if c.isClassDef then c.caseFields.map(f => fieldDef(c, f, pos)) else Nil
            CtorDef(cleanName(c.name), fields, doc(c))
          })
        else
          if sym.declaredTypes.exists(_.isTypeParam) then fail(s"generic ADTs are not supported: ${sym.name}", pos)
          AdtShape.Product(sym.caseFields.map(f => fieldDef(sym, f, pos)))
      val custom = List("equals", "hashCode").flatMap(sym.declaredMethod).filterNot(_.flags.is(Flags.Synthetic))
      if custom.nonEmpty then
        fail(s"${sym.name} overrides ${custom.map(_.name).mkString(" and ")}: Scala == would not be the structural equality of the translation", pos)
      adts(name) = AdtDef(name, sym.fullName, shape, doc(sym), source(sym))
      adtsInProgress -= name
    name

  private def fieldDef(cls: Symbol, f: Symbol, pos: Position): FieldDef =
    FieldDef(sanitize(f.name), tpe(cls.typeRef.memberType(f), pos), paramDoc(cls, f.name))

  // ---------------------------------------------------------------------------
  // User definitions
  // ---------------------------------------------------------------------------

  private def isUserDef(sym: Symbol): Boolean =
    !isLibrary(sym) && !sym.flags.is(Flags.Module) && !sym.flags.is(Flags.Package) && (
      isAdtClass(sym.owner) || (sym.owner.flags.is(Flags.Module) && !sym.owner.flags.is(Flags.Package))
    )

  private def isCaseField(cls: Symbol, sym: Symbol): Boolean =
    cls.caseFields.exists(_.name == sym.name) && (sym.flags.is(Flags.CaseAccessor) || sym.flags.is(Flags.ParamAccessor) || !sym.flags.is(Flags.Method))

  private def registerFun(sym: Symbol, pos: Position): String =
    val name = leanName(sym)
    claim(name, sym, pos)
    if !funs.contains(name) && !funsInProgress(name) then
      funsInProgress += name
      val tree =
        try sym.tree
        catch case _: Throwable => fail(s"cannot read the definition of ${sym.fullName}; compile with -Yretain-trees", pos)
      val owner = sym.owner
      val selfParam =
        if isAdtClass(owner) then List(Param("self", Type.Named(registerAdt(owner, pos)))) else Nil
      val selfSym = if selfParam.nonEmpty then Some(owner) else None
      val fd = tree match
        case DefDef(_, paramss, tpt, Some(rhs)) =>
          paramss.foreach {
            case TypeParamClause(_) => fail(s"${sym.name}: methods with type parameters are not supported", tree.pos)
            case c: TermParamClause if c.isGiven || c.isImplicit =>
              fail(s"${sym.name}: context parameters are not supported", tree.pos)
            case _ => ()
          }
          val vparams = paramss.collect { case TermParamClause(ps) => ps }.flatten
          val env = Env(vparams.map(v => v.symbol -> sanitize(v.name)).toMap, Map.empty, selfSym)
          val params = selfParam ++ vparams.map(v => Param(sanitize(v.name), tpe(v.tpt.tpe, v.pos)))
          FunDef(name, sym.fullName, params, tpe(tpt.tpe, tree.pos), term(rhs, env), doc(sym), source(sym))
        case ValDef(_, tpt, Some(rhs)) =>
          FunDef(name, sym.fullName, selfParam, tpe(tpt.tpe, tree.pos), term(rhs, Env(Map.empty, Map.empty, selfSym)), doc(sym), source(sym))
        case _ =>
          fail(s"cannot read the definition of ${sym.fullName}; it must be a def or val with a body (compile with -Yretain-trees)", pos)
      funs(name) = fd
      funsInProgress -= name
    name

  // ---------------------------------------------------------------------------
  // Terms
  // ---------------------------------------------------------------------------

  final case class Env(vars: Map[Symbol, String], subst: Map[Symbol, Expr], self: Option[Symbol])
  object Env:
    val empty: Env = Env(Map.empty, Map.empty, None)

  private def prim(op: Prim, args: Expr*): Expr = Expr.PrimOp(op, args.toList, None)
  private def primT(op: Prim, t: TypeRepr, args: Expr*): Expr = Expr.PrimOp(op, args.toList, tryTpe(t))

  def term(t: Term, env: Env): Expr = t match
    case Inlined(_, bindings, body) =>
      val env2 = bindings.foldLeft(env) {
        case (e, vd @ ValDef(_, _, Some(rhs))) => e.copy(subst = e.subst + (vd.symbol -> term(rhs, e)))
        case (_, other)                       => fail("unsupported inline binding", other.pos)
      }
      term(body, env2)
    case Typed(e, _)           => term(e, env)
    case NamedArg(_, e)        => term(e, env)
    case Lambda(params, body)  => lambda(params, body, env)
    case Block(Nil, e)         => term(e, env)
    case Block(stats, e)       => block(stats, e, env)
    case Literal(c)            => literal(c, t.pos)
    case If(c, a, b)           => Expr.If(term(c, env), term(a, env), term(b, env))
    case Match(sc, cases)      => matchExpr(sc, cases, env)
    case This(_) =>
      if env.self.contains(t.symbol) then Expr.Var("self")
      else fail("`this` is only supported inside methods of ADTs", t.pos)
    case _: Ident | _: Select | _: Apply | _: TypeApply => application(t, env)
    case _ => fail(s"unsupported expression: ${t.show}", t.pos)

  private def literal(c: Constant, pos: Position): Expr = c.value match
    case b: Boolean => Expr.BoolLit(b)
    case i: Int     => Expr.IntLit(BigInt(i))
    case l: Long    => Expr.IntLit(BigInt(l))
    case s: String  => Expr.StrLit(s)
    case _: Unit    => Expr.UnitLit
    case other      => fail(s"unsupported literal $other", pos)

  private def lambda(params: List[ValDef], body: Term, env: Env): Expr =
    val ps = params.map(v => Param(sanitize(v.name), tpe(v.tpt.tpe, v.pos)))
    val env2 = env.copy(vars = env.vars ++ params.map(v => v.symbol -> sanitize(v.name)))
    Expr.Lam(ps, term(body, env2))

  private def block(stats: List[Statement], e: Term, env: Env): Expr =
    stats match
      case Nil => term(e, env)
      case (vd @ ValDef(name, tpt, Some(rhs))) :: rest =>
        if vd.symbol.flags.is(Flags.Mutable) then fail("`var` is not supported", vd.pos)
        val value = term(rhs, env)
        if vd.symbol.flags.is(Flags.Synthetic) || name.contains('$') then
          block(rest, e, env.copy(subst = env.subst + (vd.symbol -> value)))
        else
          val n = sanitize(name)
          Expr.Let(n, tpe(tpt.tpe, vd.pos), value, block(rest, e, env.copy(vars = env.vars + (vd.symbol -> n))))
      case other :: _ => fail("only `val` definitions are supported inside blocks", other.pos)

  private def matchExpr(sc: Term, cases: List[CaseDef], env: Env): Expr =
    Expr.Match(term(sc, env), cases.map { cd =>
      if cd.guard.nonEmpty then fail("case guards are not supported", cd.pos)
      val (pat, binds) = pattern(cd.pattern)
      Case(pat, term(cd.rhs, env.copy(vars = env.vars ++ binds)))
    })

  private def pattern(p: Tree): (Pattern, Map[Symbol, String]) = p match
    case Wildcard() => (Pattern.Wild, Map.empty)
    case b @ Bind(name, inner) =>
      val (ip, bs) = pattern(inner)
      val n = sanitize(name)
      (Pattern.Bind(n, ip), bs + (b.symbol -> n))
    case TypedOrTest(inner, _) => pattern(inner)
    case Unapply(fun, _, pats) =>
      val subs = pats.map(pattern)
      (Pattern.Ctor(unapplyCtor(fun), subs.map(_._1)), subs.flatMap(_._2).toMap)
    case Literal(c) => (Pattern.Lit(literal(c, p.pos)), Map.empty)
    case t: Term if isEnumSingleton(t.symbol) => (Pattern.Ctor(registerEnumCase(t.symbol, t.pos), Nil), Map.empty)
    case t: Term if isNone(t.symbol)          => (Pattern.Ctor("none", Nil), Map.empty)
    case t: Term if isNil(t.symbol)           => (Pattern.Ctor("[]", Nil), Map.empty)
    case _ => fail(s"unsupported pattern: ${p.show}", p.pos)

  private def unapplyCtor(fun: Term): String =
    if !fun.symbol.flags.is(Flags.Synthetic) && !isLibrary(fun.symbol) then
      fail(s"custom extractor ${fun.symbol.fullName} cannot be translated; match on constructors", fun.pos)
    val qual = fun match
      case Select(q, "unapply")                 => q
      case TypeApply(Select(q, "unapply"), _)   => q
      case _                                    => fail(s"unsupported extractor: ${fun.show}", fun.pos)
    val cls = norm(qual.tpe).typeSymbol.companionClass
    if cls == TypeRepr.of[Some[Any]].typeSymbol then "some"
    else if cls == TypeRepr.of[::[Any]].typeSymbol then "::"
    else if defn.isTupleClass(cls) then "tuple"
    else if isAdtClass(cls) then leanName(registerAdtFor(cls, fun.pos)) + ".mk"
    else if cls.flags.is(Flags.Case) && cls.flags.is(Flags.Enum) then registerEnumCase(cls, fun.pos)
    else fail(s"unsupported extractor: ${fun.show}", fun.pos)

  private def registerAdtFor(cls: Symbol, pos: Position): Symbol =
    registerAdt(cls, pos)
    cls

  private def isEnumSingleton(sym: Symbol): Boolean =
    sym.isTerm && sym.flags.is(Flags.Enum) && sym.flags.is(Flags.Case) && !sym.flags.is(Flags.Module) && !isLibrary(sym)

  /** Registers the enum a case belongs to and returns the constructor's Lean name. */
  private def registerEnumCase(caseSym: Symbol, pos: Position): String =
    val enumCls = if caseSym.isClassDef then caseSym.owner.companionClass else norm(caseSym.termRef).typeSymbol
    val enumSym = if isAdtClass(enumCls) then enumCls else caseSym.owner.companionClass
    registerAdt(enumSym, pos)
    leanName(caseSym)

  private def isNone(sym: Symbol): Boolean = sym.name == "None" && sym.fullName.startsWith("scala.")
  private def isNil(sym: Symbol): Boolean = sym.name == "Nil" && sym.fullName.startsWith("scala.")

  // ---------------------------------------------------------------------------
  // Applications: method calls, constructors, built-in operations
  // ---------------------------------------------------------------------------

  private def spine(t: Term): (Term, List[List[Term]]) = t match
    case Apply(f, args)  => val (h, as) = spine(f); (h, as :+ args)
    case TypeApply(f, _) => spine(f)
    case _               => (t, Nil)

  /** Implicit wrappers whose argument is the real receiver. */
  private val wrappers = Set(
    "scala.Predef.augmentString", "scala.Predef.intWrapper", "scala.Predef.longWrapper", "scala.Predef.ArrowAssoc",
    "scala.LowPriorityImplicits.intWrapper", "scala.LowPriorityImplicits.longWrapper"
  )
  private val widenings = Set(
    "scala.Int.int2long", "scala.math.BigInt.int2bigInt", "scala.math.BigInt.long2bigInt"
  )

  private def unwrap(t: Term): Term = t match
    case Inlined(_, Nil, b) => unwrap(b)
    case Typed(e, _)        => unwrap(e)
    case _ =>
      spine(t) match
        case (h, List(List(arg))) if wrappers(h.symbol.fullName) || widenings(h.symbol.fullName) => unwrap(arg)
        case _ => t

  private def companionOf(q: Term): Symbol = norm(q.tpe).typeSymbol.companionClass

  private def varargs(args: List[Term]): List[Term] = args match
    case List(Typed(Repeated(es, _), _)) => es
    case List(Repeated(es, _))           => es
    case List(Inlined(_, Nil, x))        => varargs(List(x))
    case other                           => other

  private def application(t: Term, env: Env): Expr =
    val (head, argss) = spine(t)
    val args = argss.flatten
    def tr(x: Term): Expr = term(x, env)
    val sym = head.symbol
    lazy val name = sym.name
    lazy val recv: Option[Term] = head match
      case Select(q, _) => Some(unwrap(q))
      case _            => None

    // local variables and inlined values
    if argss.isEmpty && env.subst.contains(sym) then return env.subst(sym)
    if argss.isEmpty && env.vars.contains(sym) then return Expr.Var(env.vars(sym))

    head match
      case Select(New(tpt), "<init>") => return construct(tpt.tpe.typeSymbol, args.map(tr), t.pos)
      case _                          => ()

    // specification logic from frflow.dsl
    if sym.fullName.startsWith("frflow.dsl.") then
      (name, argss) match
        case ("forall" | "exists", List(List(f))) =>
          tr(f) match
            case Expr.Lam(ps, b) => return Expr.Quant(if name == "forall" then Quantifier.All else Quantifier.Ex, ps, b)
            case _               => fail(s"$name expects a lambda", f.pos)
        case ("==>", List(List(a), List(b))) => return prim(Prim.Implies, tr(a), tr(b))
        case _                               => fail(s"unsupported use of ${sym.fullName}", t.pos)

    if widenings(sym.fullName) && args.size == 1 then return tr(args.head)

    // equality
    if (name == "==" || name == "!=") && recv.isDefined && args.size == 1 then
      return prim(if name == "==" then Prim.Eq else Prim.Ne, tr(recv.get), tr(args.head))

    // tuples built with ->
    if name == "->" && recv.isDefined && args.size == 1 then
      return prim(Prim.TupleOf, tr(recv.get), tr(args.head))

    // nullary built-in values
    if argss.isEmpty then
      if isNone(sym) then return primT(Prim.OptNone, t.tpe)
      if isNil(sym) then return primT(Prim.ListNil, t.tpe)
      if isEnumSingleton(sym) then return Expr.Construct(registerEnumCase(sym, t.pos), Nil)

    // companions: constructors of collections and ADTs
    head match
      case Select(q, "empty") if q.tpe.widen.typeSymbol.flags.is(Flags.Module) =>
        val c = companionOf(q)
        if c == ListSym then return primT(Prim.ListNil, t.tpe)
        if c == SetSym then return primT(Prim.SetEmpty, t.tpe)
        if c == MapSym then return primT(Prim.MapEmpty, t.tpe)
      case Select(q, "apply") if q.tpe.widen.typeSymbol.flags.is(Flags.Module) =>
        val c = companionOf(q)
        if c == ListSym then return primT(Prim.ListOf, t.tpe, varargs(args).map(tr)*)
        if c == SetSym then return primT(Prim.SetOf, t.tpe, varargs(args).map(tr)*)
        if c == MapSym then
          val empty = primT(Prim.MapEmpty, t.tpe)
          return varargs(args).map(tr).foldLeft(empty) { (m, kv) =>
            kv match
              case Expr.PrimOp(Prim.TupleOf, List(k, v), _) => prim(Prim.MapUpdated, m, k, v)
              case other                                    => prim(Prim.MapUpdated, m, prim(Prim.Fst, other), prim(Prim.Snd, other))
          }
        if c == TypeRepr.of[Some[Any]].typeSymbol then return prim(Prim.OptSome, tr(args.head))
        if defn.isTupleClass(c) then return prim(Prim.TupleOf, args.map(tr)*)
        if (isAdtClass(c) || (c.flags.is(Flags.Case) && c.flags.is(Flags.Enum) && !isLibrary(c))) && sym.flags.is(Flags.Synthetic) then
          return construct(c, args.map(tr), t.pos)
      case _ => ()

    // default arguments
    if name.contains("$default$") then return defaultArg(head, sym, env, t.pos)

    // receiver-based operations
    recv match
      case Some(q) =>
        val qt = norm(q.tpe)
        val qs = qt.typeSymbol
        if isAdtClass(qs) && qs.flags.is(Flags.Case) && args.isEmpty && qs.caseFields.exists(_.name == name) then
          return Expr.Field(tr(q), sanitize(name))
        if isAdtClass(qs) && name == "copy" then
          if !sym.flags.is(Flags.Synthetic) then fail(s"${qs.name} defines its own copy, which FrFlow cannot translate", t.pos)
          return copyExpr(q, qs, argss, env, t.pos)
        builtin(q, qt, name, args, env, t) match
          case Some(e) => return e
          case None    => ()
        if qt.isFunctionType && name == "apply" then return Expr.App(tr(q), args.map(tr))
      case None => ()

    // fields of `this` inside a method
    if env.self.isDefined && sym.owner == env.self.get && argss.isEmpty && isCaseField(env.self.get, sym) then
      return Expr.Field(Expr.Var("self"), sanitize(name))

    // user methods and functions
    if isUserDef(sym) then
      val fn = registerFun(sym, t.pos)
      val isMethod = isAdtClass(sym.owner)
      val receiver: List[Expr] =
        if !isMethod then Nil
        else
          head match
            case Select(q, _) => List(tr(q))
            case _ =>
              if env.self.contains(sym.owner) then List(Expr.Var("self"))
              else fail(s"cannot call ${sym.name} without a receiver", t.pos)
      if !isMethod && argss.isEmpty then return Expr.Ref(fn)
      return Expr.Call(fn, receiver ++ args.map(tr), isMethod)

    if !sym.isNoSymbol && sym.owner.isTerm && !sym.flags.is(Flags.Module) then
      fail(s"`${sym.name}` is defined outside the expression; move it into an object or pass it as a parameter", t.pos)
    fail(s"unsupported call: ${t.show} (${sym.fullName})", t.pos)

  private def construct(cls: Symbol, args: List[Expr], pos: Position): Expr =
    if isAdtClass(cls) && cls.flags.is(Flags.Case) then
      Expr.Construct(registerAdt(cls, pos) + ".mk", args)
    else if cls.flags.is(Flags.Case) && cls.flags.is(Flags.Enum) && !isLibrary(cls) then
      Expr.Construct(registerEnumCase(cls, pos), args)
    else fail(s"cannot construct ${cls.fullName}: only case classes and enum cases are supported", pos)

  private def copyExpr(q: Term, cls: Symbol, argss: List[List[Term]], env: Env, pos: Position): Expr =
    registerAdt(cls, pos)
    val recvE = term(q, env)
    val fields = cls.caseFields.map(_.name)
    val args = argss match
      case List(as) => as
      case _        => fail("unsupported copy", pos)
    val updates = fields.zip(args).flatMap { (f, a) =>
      val e = term(a, env)
      if e == Expr.Field(recvE, sanitize(f)) then None else Some(sanitize(f) -> e)
    }
    if updates.isEmpty then recvE else Expr.With(recvE, updates)

  private def defaultArg(head: Term, sym: Symbol, env: Env, pos: Position): Expr =
    val n = sym.name
    val idx = n.substring(n.lastIndexOf('$') + 1).toInt - 1
    if n.startsWith("copy$default$") then
      head match
        case Select(q, _) =>
          val cls = norm(q.tpe).typeSymbol
          val f = cls.caseFields(idx).name
          Expr.Field(term(q, env), sanitize(f))
        case _ => fail("unsupported copy default", pos)
    else
      val tree =
        try sym.tree
        catch case _: Throwable => fail(s"cannot read default argument ${sym.fullName}", pos)
      tree match
        case DefDef(_, Nil, _, Some(rhs)) => term(rhs, Env.empty)
        case _                            => fail(s"unsupported default argument ${sym.fullName}", pos)

  // ---------------------------------------------------------------------------
  // Built-in operations on standard types
  // ---------------------------------------------------------------------------

  private def builtin(q: Term, qt: TypeRepr, name: String, args: List[Term], env: Env, whole: Term): Option[Expr] =
    def tr(x: Term): Expr = term(x, env)
    lazy val r = tr(q)
    def p(op: Prim, xs: Expr*): Option[Expr] = Some(prim(op, xs*))
    def a(i: Int): Expr = tr(args(i))
    val n = args.size
    def unsupported: Nothing = fail(s"unsupported operation `$name` on ${qt.show}", whole.pos)

    if qt =:= TypeRepr.of[Boolean] then
      (name, n) match
        case ("&&", 1)      => p(Prim.And, r, a(0))
        case ("||", 1)      => p(Prim.Or, r, a(0))
        case ("unary_!", 0) => p(Prim.Not, r)
        case ("^", 1)       => p(Prim.Ne, r, a(0))
        case _              => unsupported
    else if isInt(qt) then
      (name, n) match
        case ("+", 1)  => p(Prim.Add, r, a(0))
        case ("-", 1)  => p(Prim.Sub, r, a(0))
        case ("*", 1)  => p(Prim.Mul, r, a(0))
        case ("/", 1)  => p(Prim.Div, r, a(0))
        case ("%", 1)  => p(Prim.Mod, r, a(0))
        case ("<", 1)  => p(Prim.Lt, r, a(0))
        case ("<=", 1) => p(Prim.Le, r, a(0))
        case (">", 1)  => p(Prim.Gt, r, a(0))
        case (">=", 1) => p(Prim.Ge, r, a(0))
        case ("max", 1) => p(Prim.Max, r, a(0))
        case ("min", 1) => p(Prim.Min, r, a(0))
        case ("unary_-", 0) => p(Prim.Neg, r)
        case ("toInt" | "toLong", 0) => Some(r)
        case _ => unsupported
    else if qt =:= TypeRepr.of[String] then
      (name, n) match
        case ("+", 1) if norm(args(0).tpe) =:= TypeRepr.of[String] => p(Prim.Concat, r, a(0))
        case ("isEmpty", 0)  => p(Prim.Eq, r, Expr.StrLit(""))
        case ("nonEmpty", 0) => p(Prim.Ne, r, Expr.StrLit(""))
        case _               => unsupported
    else if qt.derivesFrom(ListSym) then
      (name, n) match
        case ("::", 1)                          => p(Prim.ListCons, a(0), r)
        case (":::", 1)                         => p(Prim.ListAppend, a(0), r)
        case ("++" | "appendedAll" | "concat", 1) => p(Prim.ListAppend, r, a(0))
        case ("contains", 1)                    => p(Prim.ListContains, r, a(0))
        case ("forall", 1)                      => p(Prim.ListForall, r, a(0))
        case ("exists", 1)                      => p(Prim.ListExists, r, a(0))
        case ("map", 1)                         => p(Prim.ListMap, r, a(0))
        case ("filter", 1)                      => p(Prim.ListFilter, r, a(0))
        case ("length" | "size", 0)             => p(Prim.ListLength, r)
        case ("isEmpty", 0)                     => p(Prim.ListIsEmpty, r)
        case ("nonEmpty", 0)                    => p(Prim.ListNonEmpty, r)
        case ("headOption", 0)                  => p(Prim.ListHeadOption, r)
        case _                                  => unsupported
    else if qt.derivesFrom(OptionSym) then
      (name, n) match
        case ("getOrElse", 1)               => p(Prim.OptGetOrElse, r, a(0))
        case ("isDefined" | "nonEmpty", 0)  => p(Prim.OptIsDefined, r)
        case ("isEmpty", 0)                 => p(Prim.OptIsEmpty, r)
        case ("contains", 1)                => p(Prim.OptContains, r, a(0))
        case ("exists", 1)                  => p(Prim.OptExists, r, a(0))
        case ("forall", 1)                  => p(Prim.OptForall, r, a(0))
        case ("map", 1)                     => p(Prim.OptMap, r, a(0))
        case ("flatMap", 1)                 => p(Prim.OptFlatMap, r, a(0))
        case ("orElse", 1)                  => p(Prim.OptOrElse, r, a(0))
        case _                              => unsupported
    else if qt.derivesFrom(SetSym) then
      (name, n) match
        case ("contains" | "apply", 1)                => p(Prim.SetContains, r, a(0))
        case ("+" | "incl", 1)                        => p(Prim.SetIncl, r, a(0))
        case ("-" | "excl", 1)                        => p(Prim.SetExcl, r, a(0))
        case ("++" | "union" | "|" | "concat", 1)     => p(Prim.SetUnion, r, a(0))
        case ("intersect" | "&", 1)                   => p(Prim.SetIntersect, r, a(0))
        case ("diff" | "--" | "&~" | "removedAll", 1) => p(Prim.SetDiff, r, a(0))
        case ("forall", 1)                            => p(Prim.SetForall, r, a(0))
        case ("exists", 1)                            => p(Prim.SetExists, r, a(0))
        case ("isEmpty", 0)                           => p(Prim.SetIsEmpty, r)
        case ("nonEmpty", 0)                          => p(Prim.Not, prim(Prim.SetIsEmpty, r))
        case ("subsetOf", 1)                          => p(Prim.SetSubsetOf, r, a(0))
        case _                                        => unsupported
    else if qt.derivesFrom(MapSym) then
      (name, n) match
        case ("get", 1)                       => p(Prim.MapGet, r, a(0))
        case ("getOrElse", 2)                 => p(Prim.MapGetOrElse, r, a(0), a(1))
        case ("updated", 2)                   => p(Prim.MapUpdated, r, a(0), a(1))
        case ("+", 1) =>
          a(0) match
            case Expr.PrimOp(Prim.TupleOf, List(k, v), _) => p(Prim.MapUpdated, r, k, v)
            case kv                                       => p(Prim.MapUpdated, r, prim(Prim.Fst, kv), prim(Prim.Snd, kv))
        case ("removed" | "-", 1)             => p(Prim.MapRemoved, r, a(0))
        case ("contains" | "isDefinedAt", 1)  => p(Prim.MapContains, r, a(0))
        case ("isEmpty", 0)                   => p(Prim.MapIsEmpty, r)
        case ("nonEmpty", 0)                  => p(Prim.Not, prim(Prim.MapIsEmpty, r))
        case ("forall", 1)                    => p(Prim.MapForall, r, a(0))
        case ("exists", 1)                    => p(Prim.MapExists, r, a(0))
        case ("keySet", 0)                    => p(Prim.MapKeySet, r)
        case _                                => unsupported
    else if defn.isTupleClass(qt.typeSymbol) then
      (name, n) match
        case ("_1", 0) => p(Prim.Fst, r)
        case ("_2", 0) => p(Prim.Snd, r)
        case _         => unsupported
    else None
