package frflow.lift

import frflow.*
import scala.annotation.tailrec
import scala.quoted.*

/** Translates one Scala lambda (or a `define`'s) to a Lean term. */
private[lift] final class Translator(using q: Quotes) extends TypeTranslation(using q):
  import quotes.reflect.*
  private type Env = Map[Symbol, String]

  // The negations (`!`, the left of `==>`) the term is under: a `forall` under an odd number says something
  // exists. A counter of this expansion, like the buffers, rather than a parameter of every case of `expr`.
  private var negations = 0
  private def negated[T](f: => T): T = { negations += 1; try f finally negations -= 1 }

  def lift[F: Type](f: Expr[F]): Expr[Lifted[F]] =
    val term = strip(f.asTerm)
    val ft = TypeRepr.of[F].dealias
    val (params, body) = term match
      case Lambda(ps, b) =>
        val names = ps.map(p => local(p.symbol, p.pos))
        (ps.zip(names).map((p, n) => n -> tpe(p.tpt.tpe, p.pos)), expr(b, ps.map(_.symbol).zip(names).toMap))
      case other => (Nil, expr(other, Map.empty))
    checkCapture()
    val result = tpe(if ft.isFunctionType then ft.typeArgs.last else ft, term.pos)
    val depList = Expr.ofList(deps.toList.map(_.asExprOf[Def[?]]))
    val paramList = Expr.ofList(paramTerms.toList.map(_.asExprOf[Param[?]]))
    val opaqueList = Expr.ofList(opaqueTerms.values.toList.map(_.asExprOf[Opaque]))
    // Built in a method of its own: a file's top-level vals all initialize in one JVM method, which may not
    // exceed 64 KB; the construction is the bulk of each node's expansion.
    '{
      def liftedNode(): Lifted[F] =
        new Lifted[F](() => $f, ${ Expr(params) }, ${ Expr(result) }, ${ Expr(body) }, ${ Expr(source(term match { case Lambda(Nil, b) => strip(b).pos; case t => t.pos })) }, $typeList,
          ${ Expr(opaques.toList) }, ${ Expr(paramRefs.toList) }, () => $depList, () => $paramList, () => $opaqueList)
      liftedNode()
    }

  def defName: String =
    @tailrec def named(s: Symbol): Symbol =
      if !s.isNoSymbol && (s.flags.is(Flags.Synthetic) || s.name.startsWith("$") || s.name == "macro" || !s.isTerm) then named(s.owner) else s
    val s = named(Symbol.spliceOwner)
    if s.isNoSymbol || !s.isValDef then fail("`define` must be assigned to a val", Position.ofMacroExpansion)
    // Its Lean name comes from where it is declared: a val inside a method or a lambda has none.
    def inBody(o: Symbol): Boolean = !o.isNoSymbol && !o.isPackageDef && (o.isDefDef || inBody(o.owner))
    if inBody(s.owner) then fail("`define` must be a top-level val, or a val of an object", Position.ofMacroExpansion)
    qualifiedName(s)
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
      val names = ps.map(v => local(v.symbol, v.pos))
      val bs = ps.zip(names).map((v, n) => s"($n : ${tpe(v.tpt.tpe, v.pos)})").mkString(" ")
      p(s"fun $bs => ${expr(b, env ++ ps.map(_.symbol).zip(names))}")
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
      else
        val n = local(v.symbol, v.pos)
        p(s"let $n : ${tpe(tpt.tpe, v.pos)} := $value; ${block(rest, e, env + (v.symbol -> n))}")
    case other :: _ => fail("only `val` definitions are supported in blocks", other.pos)

  private def literal(c: Constant, pos: Position): String = c.value match
    case b: Boolean => if b then "True" else "False"
    case i: Int     => if i < 0 then p(i.toString) else i.toString
    case l: Long    => if l < 0 then p(l.toString) else l.toString
    // The call markers ⟦ ⟧ the generator resolves are escaped, so a string can never be read as a call.
    case s: String  => Names.string(s)
    case _: Unit    => "()"
    case other      => fail(s"literal $other is not supported", pos)

  private def caseDef(cd: CaseDef, env: Env): String =
    if cd.guard.nonEmpty then fail("case guards are not supported", cd.pos)
    val (pat, binds) = pattern(cd.pattern)
    s"| $pat => ${expr(cd.rhs, env ++ binds)}"

  private def pattern(t: Tree): (String, Env) = t match
    case Wildcard() => ("_", Map.empty)
    case b @ Bind(_, Wildcard()) => val n = local(b.symbol, b.pos); (n, Map(b.symbol -> n))
    case b @ Bind(_, inner) =>
      val (ip, bs) = pattern(inner)
      val n = local(b.symbol, b.pos)
      (s"$n@${p(ip)}", bs + (b.symbol -> n))
    // A type test would match anything in Lean: refused, unless the type says nothing new.
    case TypedOrTest(inner, tpt) =>
      inner match
        case _: Unapply => pattern(inner) // a constructor pattern: Lean matches the constructor itself
        case _ => fail(s"a type test in a pattern is not supported in a model: match on the case itself (as in `case Shape.Circle(r)`)", t.pos)
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
    // true and false are not constructors in Lean (a Boolean is a Prop there): they would bind a variable.
    case Literal(c) if c.value.isInstanceOf[Boolean] => fail("matching on true or false is not supported in a model: use if", t.pos)
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

  /** `N.mk` of a case class, `E.C` of an enum case with fields. */
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

  private def pair(t: Term, env: Env): (String, String) = strip(t) match
    case Apply(TypeApply(Select(Apply(TypeApply(arrow, _), List(k)), "->"), _), List(v)) if arrow.symbol.name == "ArrowAssoc" =>
      (expr(k, env), expr(v, env))
    case other =>
      val x = expr(other, env)
      (s"($x).1", s"($x).2")

  private def varargs(as: List[Term]): List[Term] = as match
    case List(Typed(Repeated(es, _), _)) => es
    case List(Repeated(es, _))           => es
    case other                           => other
  // Each step of `app` is tried in turn, until one translates the term.
  private def when(cond: Boolean)(x: => Option[String]): Option[String] = if cond then x else None

  private def app(t: Term, env: Env): String =
    val (head, argss) = spine(t)
    val sym = head.symbol
    val name = sym.name
    val args = argss.flatten
    def e(x: Term) = expr(x, env)
    val recv = head match
      case Select(q, _) => Some(unwrap(q))
      case _            => None
    def isParam(x: Term) = norm(x.tpe).typeSymbol.fullName == "frflow.Param"

    when(argss.isEmpty)(env.get(sym))
      .orElse(when(Set("int2long", "int2bigInt", "long2bigInt")(name) && args.size == 1)(Some(e(args.head))))
      // calls of defined functions and parameters: `d(a, b)` is an `apply` extension of `frflow`
      .orElse(when(name == "apply" && sym.owner.fullName.startsWith("frflow") && argss.size == 2) {
        val d = argss.head.head
        if !d.symbol.isValDef then fail("call a defined function or parameter through the val it is assigned to", d.pos)
        val head =
          if isParam(d) then paramRef(d)
          else { deps += d; s"⟦${qualifiedName(d.symbol)}⟧" }
        Some(p((head :: argss(1).map(e)).mkString(" ")))
      })
      .orElse(recv.filter(q => name == "value" && argss.isEmpty && isParam(q)).map(paramRef))
      .orElse(when(sym.fullName.startsWith("frflow."))(logic(name, argss, env)))
      .orElse(recv.filter(_ => (name == "==" || name == "!=") && args.size == 1)
        .map(q => p(s"${e(q)} ${if name == "==" then "=" else "≠"} ${e(args.head)}")))
      .orElse(head match
        case Select(New(tpt), "<init>") => Some(p((ctorName(tpt.tpe.typeSymbol, t.pos) :: args.map(e)).mkString(" ")))
        case _                          => None)
      // values and companions of the standard library and of the domain
      .orElse(when(argss.isEmpty) {
        if isNamed(sym, "None") then Some("none")
        else if isNamed(sym, "Nil") then Some("[]")
        else if isEnumValue(sym) then Some(enumValue(sym, t.pos))
        else None
      })
      .orElse(companion(t, head, args, env))
      .orElse(when(name.startsWith("copy$default$")) {
        val q = recv.getOrElse(unsupported(t))
        val idx = name.stripPrefix("copy$default$").toInt - 1
        Some(s"${e(q)}.${ident(norm(q.tpe).typeSymbol.caseFields(idx).name)}")
      })
      .getOrElse(member(t, recv, sym, args, env))

  private def logic(name: String, argss: List[List[Term]], env: Env): Option[String] =
    def e(x: Term) = expr(x, env)
    (name, argss) match
      case ("forall" | "exists", List(List(f))) =>
        strip(f) match
          case Lambda(vs, b) =>
            val q = if name == "forall" then "∀" else "∃"
            // Lean's integers are unbounded: a value Lean shows to exist (larger than every Long) may not in Scala.
            if name == "exists" || negations % 2 == 1 then vs.find(v => bounded(v.tpt.tpe)).foreach(v =>
              fail(s"${if name == "exists" then "exists" else "a negated forall (it says something exists)"} over ${v.name}, whose type holds an Int or Long: Lean's integers are unbounded, Scala's are not, so what Lean finds may not exist in Scala; use BigInt", v.pos))
            val names = vs.map(v => local(v.symbol, v.pos))
            val bs = vs.zip(names).map((v, n) => s"($n : ${tpe(v.tpt.tpe, v.pos)})").mkString(" ")
            Some(p(s"$q $bs, ${expr(b, env ++ vs.map(_.symbol).zip(names))}"))
          case _ => fail(s"$name expects a lambda", f.pos)
      case ("==>", List(List(a), List(b))) => val l = negated(e(a)); Some(p(s"$l → ${e(b)}"))
      case _                               => None

  private def companion(t: Term, head: Term, args: List[Term], env: Env): Option[String] =
    def e(x: Term) = expr(x, env)
    head match
      case Select(q, "empty") if norm(q.tpe).typeSymbol.companionClass == ListSym => Some("[]")
      case Select(q, "empty") if norm(q.tpe).typeSymbol.companionClass == MapSym => Some("(fun _ => none)")
      case Select(q, "empty") if norm(q.tpe).typeSymbol.companionClass == SetSym => Some("(fun _ => False)")
      case Select(q, "apply") if norm(q.tpe).typeSymbol.flags.is(Flags.Module) =>
        val c = norm(q.tpe).typeSymbol.companionClass
        if c == ListSym then Some(varargs(args).map(e).mkString("[", ", ", "]"))
        else if c == MapSym then
          val k = unique(new Object, "k", t.pos)
          Some(p(s"fun $k => " + varargs(args).map(pair(_, env)).foldRight("none")((kv, rest) => s"if $k = ${kv._1} then some ${kv._2} else $rest")))
        else if c == SetSym then
          val y = unique(new Object, "y", t.pos)
          Some(p(s"fun $y => " + (varargs(args).map(x => s"$y = ${e(x)}") :+ "False").mkString(" ∨ ")))
        else if c == TypeRepr.of[Some[Any]].typeSymbol then Some(p(s"some ${e(args.head)}"))
        else if c == TypeRepr.of[BigInt].typeSymbol && args.size == 1 && isInt(args.head.tpe) then Some(e(args.head))
        else if defn.isTupleClass(c) then Some(args.map(e).mkString("(", ", ", ")"))
        else if head.symbol.flags.is(Flags.Synthetic) && !isLibrary(c) then Some(p((ctorName(c, t.pos) :: args.map(e)).mkString(" ")))
        else None
      case _ => None

  private def member(t: Term, recv: Option[Term], sym: Symbol, args: List[Term], env: Env): String =
    def e(x: Term) = expr(x, env)
    val name = sym.name
    recv match
      case Some(q) =>
        val qt = norm(q.tpe)
        val qs = qt.typeSymbol
        if isAdt(qs) && qs.flags.is(Flags.Case) && args.isEmpty && qs.caseFields.exists(_.name == name) then
          declare(qs, t.pos)
          s"${e(q)}.${ident(name)}"
        else if isAdt(qs) && name == "copy" && sym.flags.is(Flags.Synthetic) then
          val recvText = e(q)
          val updates = qs.caseFields.zip(args).flatMap { (f, a) =>
            val v = e(a)
            if v == s"$recvText.${ident(f.name)}" then None else Some(s"${ident(f.name)} := $v")
          }
          if updates.isEmpty then recvText else s"{ $recvText with ${updates.mkString(", ")} }"
        else if qt.isFunctionType && name == "apply" then p((e(q) :: args.map(e)).mkString(" "))
        else builtin(q, qt, name, args, env).getOrElse(unsupported(t))
      case None => unsupported(t)

  /** A parameter is a Lean variable of the same name. */
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
    def lam(f: Term): (String, String) = strip(f) match
      case Lambda(List(v), b) => val x = unique(v.symbol, ident(v.name), v.pos, free); (x, expr(b, env + (v.symbol -> x)))
      case other              => val x = unique(new Object, "x", other.pos, free); (x, s"${e(other)} $x")
    def bin(op: String) = Some(p(s"$r $op ${e(args.head)}"))
    (name, args.size) match
      case ("&&", 1) if qt =:= TypeRepr.of[Boolean]      => bin("∧")
      case ("||", 1) if qt =:= TypeRepr.of[Boolean]      => bin("∨")
      case ("unary_!", 0) if qt =:= TypeRepr.of[Boolean] => Some(p(s"¬${negated(e(q))}"))
      case ("+" | "-" | "*", 1) if isInt(qt)             => exact(qt, name, q.pos); bin(name)
      case ("/" | "%", 1) if isInt(qt) =>
        exact(qt, name, q.pos)
        if !nonZero(args.head) then fail(s"`$name` by something that may be zero: Lean gives 0, Scala throws; divide by a literal", args.head.pos)
        Some(p(s"${if name == "/" then "Int.tdiv" else "Int.tmod"} $r ${e(args.head)}"))
      case ("<", 1) if isInt(qt)                         => bin("<")
      case ("<=", 1) if isInt(qt)                        => bin("≤")
      case (">", 1) if isInt(qt)                         => bin(">")
      case (">=", 1) if isInt(qt)                        => bin("≥")
      case ("max" | "min", 1) if isInt(qt)               => Some(p(s"$name $r ${e(args.head)}"))
      case ("unary_-", 0) if isInt(qt)                   => exact(qt, "-", q.pos); Some(p(s"-$r"))
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
      case ("foldLeft", 2) if qt.derivesFrom(ListSym)    => Some(p(s"List.foldl ${e(args(1))} ${e(args.head)} $r"))
      case ("filter", 1) if qt.derivesFrom(ListSym) =>
        val (x, b) = lam(args.head); Some(p(s"List.filter (fun $x => decide $b) $r"))
      case ("filterNot", 1) if qt.derivesFrom(ListSym) =>
        val (x, b) = lam(args.head); Some(p(s"List.filter (fun $x => decide (¬$b)) $r"))
      case ("flatMap", 1) if qt.derivesFrom(ListSym)     => Some(p(s"List.flatMap ${e(args.head)} $r"))
      case ("find", 1) if qt.derivesFrom(ListSym) =>
        val (x, b) = lam(args.head); Some(p(s"List.find? (fun $x => decide $b) $r"))
      case ("headOption", 0) if qt.derivesFrom(ListSym)  => Some(p(s"List.head? $r"))
      // A list's elements as a set (its membership): built once, a hash set answers `contains` at once.
      case ("toSet", 0) if qt.derivesFrom(ListSym) =>
        val y = unique(new Object, "y", q.pos, free); Some(p(s"fun $y => $y ∈ $r"))
      // A negative count takes nothing and drops nothing, in both.
      case ("take" | "drop", 1) if qt.derivesFrom(ListSym) && isInt(args.head.tpe.widen) =>
        Some(p(s"List.$name (Int.toNat ${e(args.head)}) $r"))
      case ("zip", 1) if qt.derivesFrom(ListSym) && args.head.tpe.widen.derivesFrom(ListSym) => Some(p(s"List.zip $r ${e(args.head)}"))
      // Maps and sets, as functions: what is said of every key needs iterating them, which Lean cannot.
      case ("get", 1) if qt.derivesFrom(MapSym)          => Some(p(s"$r ${e(args.head)}"))
      case ("contains", 1) if qt.derivesFrom(MapSym)     => Some(p(s"$r ${e(args.head)} ≠ none"))
      case ("getOrElse", 2) if qt.derivesFrom(MapSym)    => Some(p(s"Option.getD ($r ${e(args.head)}) ${e(args(1))}"))
      case ("updated", 2) if qt.derivesFrom(MapSym) =>
        val x = unique(new Object, "k", q.pos, free); Some(p(s"fun $x => if $x = ${e(args.head)} then some ${e(args(1))} else $r $x"))
      case ("+", 1) if qt.derivesFrom(MapSym) =>
        val x = unique(new Object, "k", q.pos, free); val (k, v) = pair(args.head, env)
        Some(p(s"fun $x => if $x = $k then some $v else $r $x"))
      case ("removed" | "-", 1) if qt.derivesFrom(MapSym) =>
        val x = unique(new Object, "k", q.pos, free); Some(p(s"fun $x => if $x = ${e(args.head)} then none else $r $x"))
      case ("apply", 1) if qt.derivesFrom(MapSym) =>
        fail("m(k) throws in Scala when k is missing: use m.get(k) or m.getOrElse(k, default)", q.pos)
      case ("contains" | "apply", 1) if qt.derivesFrom(SetSym) => Some(p(s"$r ${e(args.head)}"))
      case ("incl" | "+", 1) if qt.derivesFrom(SetSym) =>
        val y = unique(new Object, "y", q.pos, free); Some(p(s"fun $y => $y = ${e(args.head)} ∨ $r $y"))
      case ("excl" | "-", 1) if qt.derivesFrom(SetSym) =>
        val y = unique(new Object, "y", q.pos, free); Some(p(s"fun $y => $y ≠ ${e(args.head)} ∧ $r $y"))
      case ("union" | "++" | "|", 1) if qt.derivesFrom(SetSym) =>
        val y = unique(new Object, "y", q.pos, free); Some(p(s"fun $y => $r $y ∨ ${e(args.head)} $y"))
      case ("intersect" | "&", 1) if qt.derivesFrom(SetSym) =>
        val y = unique(new Object, "y", q.pos, free); Some(p(s"fun $y => $r $y ∧ ${e(args.head)} $y"))
      case ("subsetOf", 1) if qt.derivesFrom(SetSym) =>
        val y = unique(new Object, "y", q.pos, free); Some(p(s"∀ $y, $r $y → ${e(args.head)} $y"))
      case ("forall", 1) if qt.derivesFrom(OptionSym) =>
        val (x, b) = lam(args.head); Some(p(s"∀ $x, $r = some $x → $b"))
      case ("exists", 1) if qt.derivesFrom(OptionSym) =>
        val (x, b) = lam(args.head); Some(p(s"∃ $x, $r = some $x ∧ $b"))
      case ("contains", 1) if qt.derivesFrom(OptionSym)  => Some(p(s"$r = some ${e(args.head)}"))
      case ("isDefined" | "nonEmpty", 0) if qt.derivesFrom(OptionSym) => Some(p(s"$r ≠ none"))
      case ("isEmpty", 0) if qt.derivesFrom(OptionSym)   => Some(p(s"$r = none"))
      case ("getOrElse", 1) if qt.derivesFrom(OptionSym) => Some(p(s"Option.getD $r ${e(args.head)}"))
      // Lean's A × B × C is A × (B × C): the k-th of n is k-1 steps right, then left (but the last).
      case (s"_$k", 0) if defn.isTupleClass(qt.typeSymbol) && k.toIntOption.exists(i => i >= 1 && i <= qt.typeArgs.size) =>
        val i = k.toInt
        Some(r + ".2" * (i - 1) + (if i == qt.typeArgs.size then "" else ".1"))
      case _                                             => None
