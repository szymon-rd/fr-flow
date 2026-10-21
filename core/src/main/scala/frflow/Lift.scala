package frflow

import scala.collection.mutable
import scala.quoted.*

/** Compile-time translation of Scala lambdas over domain ADTs to Lean terms.
  *
  * Supported: case classes (structures) and Scala 3 enums (inductive types);
  * `Boolean` (as `Prop`), `Int`/`Long` (as `Int`), `String`, `List`, `Option`,
  * tuples; constructors, field access, `copy`, `match`, `if`, `val`s;
  * `==`, `!=`, `&&`, `||`, `!`, `==>`, integer arithmetic and comparison; a few
  * `List`/`Option` operations; `forall`/`exists`; calls to `define`d functions;
  * opaque types (`User.T`) and parameters (`authorized(u, r)`, `shares.value`).
  * Anything else is a compile error at its position.
  */
private[frflow] object Lift:

  def lifted[F: Type](f: Expr[F])(using Quotes): Expr[Lifted[F]] = Translator().lift(f)

  def define[F: Type](f: Expr[F])(using Quotes): Expr[Def[F]] =
    val t = Translator()
    val name = t.defName
    val l = t.lift(f)
    '{ new Def[F](${ Expr(name) }, $l) }

  def leanType[T: Type](using Quotes): Expr[LeanType] = Translator().leanType[T]

  /** The source files of the project code an expression refers to (an implementation's classes). */
  def sourceFiles(e: Expr[Any])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    val files = mutable.LinkedHashSet.empty[String]
    def add(s: Symbol): Unit =
      if !s.isNoSymbol then
        s.pos.map(p => java.nio.file.Paths.get(p.sourceFile.path)).filter(java.nio.file.Files.isRegularFile(_))
          .map(_.toAbsolutePath.normalize.toString).filter(_.endsWith(".scala")).foreach(files += _)
    object T extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ref => add(r.symbol); add(r.symbol.owner)
          case n: New => add(n.tpe.typeSymbol)
          case _      => ()
        super.traverseTree(t)(owner)
    T.traverseTree(e.asTerm)(Symbol.spliceOwner)
    add(e.asTerm.tpe.widen.typeSymbol)
    val own = Some(java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path).toAbsolutePath.normalize.toString)
    Expr(files.toList.filterNot(f => f.contains("/frflow/") && f.contains("/core/src/") || own.contains(f) && files.size > 1))

  def sources(xs: Expr[Seq[Any]])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    def text(e: Expr[Any]) = e.asTerm.pos.sourceCode.getOrElse(e.show)
    xs match
      case Varargs(es) => Expr(es.map(text).toList)
      case other       => Expr(List(text(other)))

private final class Translator(using val quotes: Quotes):
  import quotes.reflect.*

  private type Env = Map[Symbol, String]
  private val types = mutable.LinkedHashMap.empty[String, TypeDecl]
  private val inProgress = mutable.Set.empty[String]
  private val deps = mutable.ListBuffer.empty[Term]
  private val paramTerms = mutable.ListBuffer.empty[Term]
  private val opaqueTerms = mutable.LinkedHashMap.empty[String, Term]
  private val opaques = mutable.LinkedHashSet.empty[String]
  private val paramRefs = mutable.LinkedHashMap.empty[String, String]

  private def fail(msg: String, pos: Position): Nothing = report.errorAndAbort(s"FrFlow: $msg", pos)
  private def unsupported(t: Tree): Nothing = fail(s"not supported in a model: ${t.show}", t.pos)

  // ---------------------------------------------------------------------------
  // Entry points
  // ---------------------------------------------------------------------------

  def lift[F: Type](f: Expr[F]): Expr[Lifted[F]] =
    val term = strip(f.asTerm)
    val ft = TypeRepr.of[F].dealias
    val (params, body) = term match
      case Lambda(ps, b) =>
        (ps.map(p => ident(p.name) -> tpe(p.tpt.tpe, p.pos)), expr(b, ps.map(p => p.symbol -> ident(p.name)).toMap))
      case other => (Nil, expr(other, Map.empty))
    val result = tpe(if ft.isFunctionType then ft.typeArgs.last else ft, term.pos)
    val depList = Expr.ofList(deps.toList.map(_.asExprOf[Def[?]]))
    val paramList = Expr.ofList(paramTerms.toList.map(_.asExprOf[Param[?]]))
    val opaqueList = Expr.ofList(opaqueTerms.values.toList.map(_.asExprOf[Opaque]))
    '{
      new Lifted[F]($f, ${ Expr(params) }, ${ Expr(result) }, ${ Expr(body) }, ${ Expr(source(term.pos)) }, $typeList,
        ${ Expr(opaques.toList) }, ${ Expr(paramRefs.toList) }, () => $depList, () => $paramList, () => $opaqueList)
    }

  def leanType[T: Type]: Expr[LeanType] =
    val lean: String = tpe(TypeRepr.of[T], Position.ofMacroExpansion)
    '{ LeanType(${ Expr(lean) }, $typeList) }

  def typeList: Expr[List[TypeDecl]] =
    Expr.ofList(types.values.toList.map(d => '{ TypeDecl(${ Expr(d.name) }, ${ Expr(d.lean) }, ${ Expr(d.uses) }) }))

  /** Lean name of the `val` a `define` is assigned to. */
  def defName: String =
    var s = Symbol.spliceOwner
    while !s.isNoSymbol && (s.flags.is(Flags.Synthetic) || s.name.startsWith("$") || s.name == "macro" || !s.isTerm) do
      s = s.owner
    if s.isNoSymbol || !s.isValDef then fail("`define` must be assigned to a val", Position.ofMacroExpansion)
    qualifiedName(s)

  private def strip(t: Term): Term = t match
    case Inlined(_, Nil, b) => strip(b)
    case Typed(e, _)        => strip(e)
    case Block(Nil, e)      => strip(e)
    case _                  => t

  private def source(pos: Position): String =
    pos.sourceCode.filter(_.nonEmpty).orElse {
      try
        val text = java.nio.file.Files.readString(java.nio.file.Paths.get(pos.sourceFile.path))
        Some(text.substring(pos.start, pos.end))
      catch case _: Throwable => None
    }.getOrElse("").trim

  // ---------------------------------------------------------------------------
  // Names
  // ---------------------------------------------------------------------------

  private val Keywords = Set(
    "at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "then", "with", "from", "show",
    "where", "open", "namespace", "section", "def", "theorem", "structure", "inductive", "instance", "import",
    "forall", "exists", "Type", "Prop", "Sort", "this", "deriving", "mut", "return", "for", "try", "catch"
  )

  def ident(n: String): String =
    val s = n.replace('$', '_')
    val t = if s.startsWith("__") then "x" + s.drop(1) else s
    if Keywords(t) then s"«$t»" else t

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

  private lazy val ListSym = TypeRepr.of[List[Any]].typeSymbol
  private lazy val OptionSym = TypeRepr.of[Option[Any]].typeSymbol

  private def norm(t: TypeRepr): TypeRepr = t.widenTermRefByName.widen.dealias

  private def isLibrary(sym: Symbol) = sym.fullName.startsWith("scala.") || sym.fullName.startsWith("java.")

  private def isAdt(sym: Symbol): Boolean =
    sym.isClassDef && !isLibrary(sym) && !sym.flags.is(Flags.Module) &&
      ((sym.flags.is(Flags.Case) && !sym.flags.is(Flags.Enum)) || (sym.flags.is(Flags.Enum) && !sym.flags.is(Flags.Case)))

  private def isInt(t: TypeRepr) = norm(t) =:= TypeRepr.of[Int] || norm(t) =:= TypeRepr.of[Long]

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
  private def declare(sym: Symbol, pos: Position): String =
    val name = qualifiedName(sym)
    if !types.contains(name) && !inProgress(name) then
      // Lean equality is structural; a class that redefines equality would mean something else at run time.
      List("equals", "hashCode").flatMap(sym.declaredMethod).filterNot(_.flags.is(Flags.Synthetic)).foreach(m =>
        fail(s"${sym.name} overrides ${m.name}: domain types must keep structural equality", pos))
      inProgress += name
      def field(cls: Symbol, f: Symbol): (String, TypeRepr) = (ident(f.name), cls.typeRef.memberType(f))
      val (lean, refs) =
        if sym.flags.is(Flags.Enum) then
          val cases = sym.children.map { c =>
            val fs = if c.isClassDef then c.caseFields.map(field(c, _)) else Nil
            (s"  | ${ident(c.name)}${fs.map((n, t) => s" ($n : ${tpe(t, pos)})").mkString}", fs.map(_._2))
          }
          (s"${doc(sym)}inductive $name where\n${cases.map(_._1).mkString("\n")}", cases.flatMap(_._2))
        else
          val fs = sym.caseFields.map(field(sym, _))
          val body = if fs.isEmpty then "" else " where\n" + fs.map((n, t) => s"  $n : ${tpe(t, pos)}").mkString("\n")
          (s"${doc(sym)}structure $name$body", fs.map(_._2))
      val uses = refs.flatMap(adtRefs).map(qualifiedName).distinct.filterNot(_ == name)
      types(name) = TypeDecl(name, lean, uses)
      inProgress -= name
    name

  // ---------------------------------------------------------------------------
  // Terms
  // ---------------------------------------------------------------------------

  private def p(s: String): String = s"($s)"

  def expr(t: Term, env: Env): String = t match
    case Inlined(_, bindings, b) =>
      expr(b, bindings.foldLeft(env) {
        case (e, v @ ValDef(_, _, Some(rhs))) => e + (v.symbol -> expr(rhs, e))
        case (_, other)                      => unsupported(other)
      })
    case Typed(e, _)          => expr(e, env)
    case NamedArg(_, e)       => expr(e, env)
    case Lambda(ps, b) =>
      val binders = ps.map(v => s"(${ident(v.name)} : ${tpe(v.tpt.tpe, v.pos)})").mkString(" ")
      p(s"fun $binders => ${expr(b, env ++ ps.map(v => v.symbol -> ident(v.name)))}")
    case Block(stats, e)      => block(stats, e, env)
    case Literal(c)           => literal(c, t.pos)
    case If(c, a, b)          => p(s"if ${expr(c, env)} then ${expr(a, env)} else ${expr(b, env)}")
    case Match(scrut, cases)  => p(s"match ${expr(scrut, env)} with ${cases.map(caseDef(_, env)).mkString(" ")}")
    case _: Ident | _: Select | _: Apply | _: TypeApply => app(t, env)
    case _                    => unsupported(t)

  private def block(stats: List[Statement], e: Term, env: Env): String = stats match
    case Nil => expr(e, env)
    case (v @ ValDef(name, tpt, Some(rhs))) :: rest =>
      if v.symbol.flags.is(Flags.Mutable) then fail("`var` is not supported", v.pos)
      val value = expr(rhs, env)
      if v.symbol.flags.is(Flags.Synthetic) || name.contains('$') then block(rest, e, env + (v.symbol -> value))
      else p(s"let ${ident(name)} : ${tpe(tpt.tpe, v.pos)} := $value; ${block(rest, e, env + (v.symbol -> ident(name)))}")
    case other :: _ => fail("only `val` definitions are supported in blocks", other.pos)

  private def literal(c: Constant, pos: Position): String = c.value match
    case b: Boolean => if b then "True" else "False"
    case i: Int     => if i < 0 then p(i.toString) else i.toString
    case l: Long    => if l < 0 then p(l.toString) else l.toString
    case s: String  => "\"" + s.flatMap { case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case ch => ch.toString } + "\""
    case _: Unit    => "()"
    case other      => fail(s"literal $other is not supported", pos)

  private def caseDef(cd: CaseDef, env: Env): String =
    if cd.guard.nonEmpty then fail("case guards are not supported", cd.pos)
    val (pat, binds) = pattern(cd.pattern)
    s"| $pat => ${expr(cd.rhs, env ++ binds)}"

  private def pattern(t: Tree): (String, Env) = t match
    case Wildcard() => ("_", Map.empty)
    case b @ Bind(n, Wildcard()) => (ident(n), Map(b.symbol -> ident(n)))
    case b @ Bind(n, inner) =>
      val (ip, bs) = pattern(inner)
      (s"${ident(n)}@${p(ip)}", bs + (b.symbol -> ident(n)))
    case TypedOrTest(inner, _) => pattern(inner)
    case Unapply(fun, _, pats) =>
      val subs = pats.map(pattern)
      val args = subs.map((s, _) => if s.contains(' ') && !s.startsWith("(") then p(s) else s)
      val qual = fun match
        case Select(q, _)              => q
        case TypeApply(Select(q, _), _) => q
        case _                         => unsupported(fun)
      val cls = norm(qual.tpe).typeSymbol.companionClass
      val text =
        if cls == TypeRepr.of[Some[Any]].typeSymbol then s"some ${args.head}"
        else if cls == TypeRepr.of[::[Any]].typeSymbol then s"${args(0)} :: ${args(1)}"
        else if defn.isTupleClass(cls) then args.mkString("(", ", ", ")")
        else if !fun.symbol.flags.is(Flags.Synthetic) then fail("custom extractors are not supported", fun.pos)
        else (ctorName(cls, fun.pos) :: args).mkString(" ")
      (text, subs.flatMap(_._2).toMap)
    case Literal(c) => (literal(c, t.pos), Map.empty)
    case r: Term if isEnumValue(r.symbol) => (enumValue(r.symbol, r.pos), Map.empty)
    case r: Term if isNamed(r.symbol, "None") => ("none", Map.empty)
    case r: Term if isNamed(r.symbol, "Nil")  => ("[]", Map.empty)
    case _ => unsupported(t)

  private def isNamed(sym: Symbol, n: String) = sym.name == n && sym.fullName.startsWith("scala.")

  private def isEnumValue(sym: Symbol) =
    sym.isTerm && sym.flags.is(Flags.Enum) && sym.flags.is(Flags.Case) && !isLibrary(sym)

  private def enumValue(sym: Symbol, pos: Position): String =
    declare(sym.owner.companionClass, pos)
    qualifiedName(sym)

  /** Lean constructor of a case class (`N.mk`) or of an enum case with fields (`E.C`). */
  private def ctorName(cls: Symbol, pos: Position): String =
    if isAdt(cls) && cls.flags.is(Flags.Case) then declare(cls, pos) + ".mk"
    else if cls.flags.is(Flags.Case) && cls.flags.is(Flags.Enum) && !isLibrary(cls) then
      declare(cls.owner.companionClass, pos)
      qualifiedName(cls)
    else fail(s"cannot construct ${cls.fullName}: only case classes and enum cases", pos)

  private def spine(t: Term): (Term, List[List[Term]]) = t match
    case Apply(f, as)    => val (h, ass) = spine(f); (h, ass :+ as)
    case TypeApply(f, _) => spine(f)
    case _               => (t, Nil)

  private def unwrap(t: Term): Term = spine(t) match
    case (h, List(List(a))) if Set("int2long", "intWrapper", "longWrapper", "augmentString")(h.symbol.name) => unwrap(a)
    case _ => t match
      case Typed(e, _)       => unwrap(e)
      case Inlined(_, Nil, b) => unwrap(b)
      case _                 => t

  private def varargs(as: List[Term]): List[Term] = as match
    case List(Typed(Repeated(es, _), _)) => es
    case List(Repeated(es, _))           => es
    case other                           => other

  private def app(t: Term, env: Env): String =
    val (head, argss) = spine(t)
    val sym = head.symbol
    val name = sym.name
    val args = argss.flatten
    def e(x: Term) = expr(x, env)
    val recv = head match
      case Select(q, _) => Some(unwrap(q))
      case _            => None

    if argss.isEmpty && env.contains(sym) then return env(sym)
    if Set("int2long")(name) && args.size == 1 then return e(args.head)

    // calls of defined functions and parameters: `d(a, b)` is an `apply` extension of `frflow`
    if name == "apply" && sym.owner.fullName.startsWith("frflow") && argss.size == 2 then
      val d = argss.head.head
      if !d.symbol.isValDef then fail("call a defined function or parameter through the val it is assigned to", d.pos)
      val head =
        if norm(d.tpe).typeSymbol.fullName == "frflow.Param" then paramRef(d)
        else { deps += d; s"⟦${qualifiedName(d.symbol)}⟧" }
      return p((head :: argss(1).map(e)).mkString(" "))
    if name == "value" && argss.isEmpty && recv.exists(q => norm(q.tpe).typeSymbol.fullName == "frflow.Param") then
      return paramRef(recv.get)

    // specification logic
    if sym.fullName.startsWith("frflow.") then
      (name, argss) match
        case ("forall" | "exists", List(List(f))) =>
          strip(f) match
            case Lambda(vs, b) =>
              val q = if name == "forall" then "∀" else "∃"
              val binders = vs.map(v => s"(${ident(v.name)} : ${tpe(v.tpt.tpe, v.pos)})").mkString(" ")
              return p(s"$q $binders, ${expr(b, env ++ vs.map(v => v.symbol -> ident(v.name)))}")
            case _ => fail(s"$name expects a lambda", f.pos)
        case ("==>", List(List(a), List(b))) => return p(s"${e(a)} → ${e(b)}")
        case _                               => ()

    if (name == "==" || name == "!=") && recv.isDefined && args.size == 1 then
      return p(s"${e(recv.get)} ${if name == "==" then "=" else "≠"} ${e(args.head)}")

    head match
      case Select(New(tpt), "<init>") => return p((ctorName(tpt.tpe.typeSymbol, t.pos) :: args.map(e)).mkString(" "))
      case _                          => ()

    // values and companions of the standard library and of the domain
    if argss.isEmpty then
      if isNamed(sym, "None") then return "none"
      if isNamed(sym, "Nil") then return "[]"
      if isEnumValue(sym) then return enumValue(sym, t.pos)
    head match
      case Select(q, "empty") if norm(q.tpe).typeSymbol.companionClass == ListSym => return "[]"
      case Select(q, "apply") if norm(q.tpe).typeSymbol.flags.is(Flags.Module) =>
        val c = norm(q.tpe).typeSymbol.companionClass
        if c == ListSym then return varargs(args).map(e).mkString("[", ", ", "]")
        if c == TypeRepr.of[Some[Any]].typeSymbol then return p(s"some ${e(args.head)}")
        if defn.isTupleClass(c) then return args.map(e).mkString("(", ", ", ")")
        if sym.flags.is(Flags.Synthetic) && !isLibrary(c) then return p((ctorName(c, t.pos) :: args.map(e)).mkString(" "))
      case _ => ()

    if name.startsWith("copy$default$") then
      val q = recv.getOrElse(unsupported(t))
      val idx = name.stripPrefix("copy$default$").toInt - 1
      return s"${e(q)}.${ident(norm(q.tpe).typeSymbol.caseFields(idx).name)}"

    recv match
      case Some(q) =>
        val qt = norm(q.tpe)
        val qs = qt.typeSymbol
        if isAdt(qs) && qs.flags.is(Flags.Case) && args.isEmpty && qs.caseFields.exists(_.name == name) then
          declare(qs, t.pos)
          return s"${e(q)}.${ident(name)}"
        if isAdt(qs) && name == "copy" && sym.flags.is(Flags.Synthetic) then
          val recvText = e(q)
          val updates = qs.caseFields.zip(args).flatMap { (f, a) =>
            val v = e(a)
            if v == s"$recvText.${ident(f.name)}" then None else Some(s"${ident(f.name)} := $v")
          }
          return if updates.isEmpty then recvText else s"{ $recvText with ${updates.mkString(", ")} }"
        if qt.isFunctionType && name == "apply" then p((e(q) :: args.map(e)).mkString(" "))
        else builtin(q, qt, name, args, env).getOrElse(unsupported(t))
      case None => unsupported(t)

  /** A reference to a parameter: a Lean variable of the same name. */
  private def paramRef(d: Term): String =
    if !d.symbol.isValDef then fail("refer to a parameter through the val it is assigned to", d.pos)
    val n = ident(d.symbol.name)
    if !paramRefs.contains(n) then
      paramRefs(n) = tpe(norm(d.tpe).typeArgs.head, d.pos)
      paramTerms += d
    n

  private def builtin(q: Term, qt: TypeRepr, name: String, args: List[Term], env: Env): Option[String] =
    def e(x: Term) = expr(x, env)
    lazy val r = e(q)
    // A binder must not capture a variable of the receiver: `∀ x ∈ r, b` puts `r` in scope of `x`.
    def free(x: String) = !(s"(?<![\\w'.])${java.util.regex.Pattern.quote(x)}(?![\\w'])").r.findFirstIn(r).isDefined
    def fresh(x: String) = (Iterator(x) ++ Iterator.from(1).map(i => s"${x}_$i")).find(free).get
    def lam(f: Term): (String, String) = strip(f) match
      case Lambda(List(v), b) => val x = fresh(ident(v.name)); (x, expr(b, env + (v.symbol -> x)))
      case other              => val x = fresh("x"); (x, s"${e(other)} $x")
    def bin(op: String) = Some(p(s"$r $op ${e(args.head)}"))
    (name, args.size) match
      case ("&&", 1) if qt =:= TypeRepr.of[Boolean]      => bin("∧")
      case ("||", 1) if qt =:= TypeRepr.of[Boolean]      => bin("∨")
      case ("unary_!", 0) if qt =:= TypeRepr.of[Boolean] => Some(p(s"¬$r"))
      case ("+", 1) if isInt(qt)                         => bin("+")
      case ("-", 1) if isInt(qt)                         => bin("-")
      case ("*", 1) if isInt(qt)                         => bin("*")
      case ("/", 1) if isInt(qt)                         => Some(p(s"Int.tdiv $r ${e(args.head)}"))
      case ("%", 1) if isInt(qt)                         => Some(p(s"Int.tmod $r ${e(args.head)}"))
      case ("<", 1) if isInt(qt)                         => bin("<")
      case ("<=", 1) if isInt(qt)                        => bin("≤")
      case (">", 1) if isInt(qt)                         => bin(">")
      case (">=", 1) if isInt(qt)                        => bin("≥")
      case ("max" | "min", 1) if isInt(qt)               => Some(p(s"$name $r ${e(args.head)}"))
      case ("unary_-", 0) if isInt(qt)                   => Some(p(s"-$r"))
      case ("+", 1) if qt =:= TypeRepr.of[String]        => bin("++")
      case ("::", 1) if qt.derivesFrom(ListSym)          => Some(p(s"${e(args.head)} :: $r"))
      case ("++", 1) if qt.derivesFrom(ListSym)          => bin("++")
      case ("contains", 1) if qt.derivesFrom(ListSym)    => Some(p(s"${e(args.head)} ∈ $r"))
      case ("isEmpty", 0) if qt.derivesFrom(ListSym)     => Some(p(s"$r = []"))
      case ("nonEmpty", 0) if qt.derivesFrom(ListSym)    => Some(p(s"$r ≠ []"))
      case ("length" | "size", 0) if qt.derivesFrom(ListSym) => Some(p(s"($r).length : Int"))
      case ("forall", 1) if qt.derivesFrom(ListSym) =>
        val (x, b) = lam(args.head); Some(p(s"∀ $x ∈ $r, $b"))
      case ("exists", 1) if qt.derivesFrom(ListSym) =>
        val (x, b) = lam(args.head); Some(p(s"∃ $x ∈ $r, $b"))
      case ("map", 1) if qt.derivesFrom(ListSym)         => Some(p(s"List.map ${e(args.head)} $r"))
      case ("filter", 1) if qt.derivesFrom(ListSym) =>
        val (x, b) = lam(args.head); Some(p(s"List.filter (fun $x => decide $b) $r"))
      case ("forall", 1) if qt.derivesFrom(OptionSym) =>
        val (x, b) = lam(args.head); Some(p(s"∀ $x, $r = some $x → $b"))
      case ("exists", 1) if qt.derivesFrom(OptionSym) =>
        val (x, b) = lam(args.head); Some(p(s"∃ $x, $r = some $x ∧ $b"))
      case ("contains", 1) if qt.derivesFrom(OptionSym)  => Some(p(s"$r = some ${e(args.head)}"))
      case ("isDefined" | "nonEmpty", 0) if qt.derivesFrom(OptionSym) => Some(p(s"$r ≠ none"))
      case ("isEmpty", 0) if qt.derivesFrom(OptionSym)   => Some(p(s"$r = none"))
      case ("getOrElse", 1) if qt.derivesFrom(OptionSym) => Some(p(s"Option.getD $r ${e(args.head)}"))
      case ("_1", 0) if defn.isTupleClass(qt.typeSymbol) => Some(s"$r.1")
      case ("_2", 0) if defn.isTupleClass(qt.typeSymbol) => Some(s"$r.2")
      case _                                             => None
