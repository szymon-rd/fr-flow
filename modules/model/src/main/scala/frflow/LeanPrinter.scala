package frflow

import frflow.types.Shape
import scala.collection.mutable

/** Prints a term's tree as Lean. Every local variable gets a name no other in the expression has (an inner one can
  * never capture an outer one), none a parameter's, an opaque type's or a type's.
  */
private[frflow] final class LeanPrinter:
  private val types = Types()
  private val paramRefs = mutable.LinkedHashMap.empty[String, String]
  private val paramObjects = mutable.ListBuffer.empty[Param[?]]
  private val defs = mutable.ListBuffer.empty[Def[?]]
  private val taken = mutable.Map.empty[String, AnyRef]
  private val binders = mutable.LinkedHashSet.empty[String]
  private val names = mutable.LinkedHashMap.empty[Binder, String]
  private val boundaries = mutable.LinkedHashSet.empty[Boundary[?]]
  // The error types the steps raise or handle: a flow's `[MonadExceptOf E m]`.
  private val errors = mutable.LinkedHashSet.empty[String]
  private var world = false
  private val commutes = mutable.ListBuffer.empty[Commute]
  // The negations (`!`, the left of `==>`) the term is under: a `forall` under an odd number says something exists.
  private var negations = 0
  private def negated[T](f: => T): T = { negations += 1; try f finally negations -= 1 }
  private def fail(msg: String): Nothing = throw IllegalArgumentException(s"FrFlow: $msg")

  def print(bs: List[Binder], body: Tree, result: LeanType[?]): Printed =
    val ns = bs.map(local)
    val params = ns.zip(bs.map(b => tpe(b.tpe)))
    val text = expr(body)
    binders.find(n => paramRefs.contains(n) || types.opaques.contains(n)).foreach(n =>
      fail(s"`$n` names both a parameter or opaque type and a local variable here; rename the local one"))
    val r = tpe(result)
    world ||= (result :: bs.map(_.tpe)).exists(Types.mentionsWorld)
    Printed(params, r, text, types.decls.values.toList, types.opaques.values.toList, paramRefs.toList, paramObjects.toList, defs.toList,
      boundaries.toList, world, errors.toList, commutes.toList)

  def tpe(t: LeanType[?]): String =
    world ||= Types.mentionsWorld(t)
    types.tpe(t)

  private def unique(owner: AnyRef, base: String, ok: String => Boolean = _ => true): String =
    // Nor a name a domain type starts with: `Share.mk` would read a field of a variable `Share`.
    // An escaped keyword (`«by»`) numbered is a plain name (`by_1`): `«by»_1` is not one.
    val stem = base.stripPrefix("«").stripSuffix("»")
    val n = (Iterator(base) ++ Iterator.from(1).map(i => s"${stem}_$i"))
      .filter(c => taken.get(c).forall(_ eq owner) && !paramRefs.contains(c) && !types.opaques.contains(c) &&
        !types.decls.keys.exists(t => t == c || t.startsWith(c + ".")) && ok(c)).next() // (the candidates never end)
    taken(n) = owner
    binders += n
    n
  private def local(b: Binder): String = { val n = unique(b, Names.ident(b.hint)); names(b) = n; n }
  private def p(s: String): String = s"($s)"

  def expr(t: Tree): String = t match
    case Tree.Var(b)          => names.getOrElse(b, fail(s"variable ${b.hint} used outside its lambda"))
    case Tree.Lit(v, lt)      => value(v, lt)
    case Tree.Ref(prm)        => paramRef(prm)
    case Tree.Call(d, args)   =>
      defs += d
      val head = s"⟦${d.name}⟧"
      p((head :: args.map(expr)).mkString(" "))
    case Tree.Apply(f, args)  => val h = expr(f); p((h :: args.map(expr)).mkString(" "))
    case Tree.Fun(bs, body)   =>
      val ns = bs.map(local)
      val typed = ns.zip(bs).map((n, b) => s"($n : ${tpe(b.tpe)})").mkString(" ")
      p(s"fun $typed => ${expr(body)}")
    case Tree.Quant(all, bs, body) =>
      if !all || negations % 2 == 1 then bs.find(b => Types.bounded(b.tpe)).foreach(b =>
        fail(s"${if !all then "exists" else "a negated forall (it says something exists)"} over ${b.hint}, whose type holds an Int or Long: Lean's integers are unbounded, Scala's are not, so what Lean finds may not exist in Scala; use BigInt"))
      val ns = bs.map(local)
      val typed = ns.zip(bs).map((n, b) => s"($n : ${tpe(b.tpe)})").mkString(" ")
      p(s"${if all then "∀" else "∃"} $typed, ${expr(body)}")
    case Tree.If(c, a, b)     => val tc = expr(c); val ta = expr(a); p(s"if $tc then $ta else ${expr(b)}")
    case Tree.Match(on, cs)   =>
      val s = expr(on)
      p(s"match $s with ${cs.map(caseDef).mkString(" ")}")
    case Tree.Let(b, v, body) =>
      val tv = expr(v)
      val n = local(b)
      val ty = tpe(b.tpe)
      p(s"let $n : $ty := $tv; ${expr(body)}")
    case Tree.Field(on, adt, i) =>
      types.declare(adt)
      s"${expr(on)}.${Names.ident(adt.ctors.head.fields(i)._1)}"
    case Tree.Copy(on, adt, ups) =>
      val r = expr(on)
      val fs = adt.ctors.head.fields
      val updates = ups.flatMap { (i, v) =>
        val tv = expr(v)
        val f = Names.ident(fs(i)._1)
        if tv == s"$r.$f" then None else Some(s"$f := $tv")
      }
      if updates.isEmpty then r else s"{ $r with ${updates.mkString(", ")} }"
    case Tree.Make(adt, c, args) =>
      types.declare(adt)
      p((c.lean :: args.map(expr)).mkString(" "))
    case Tree.Tup(es)          => es.map(expr).mkString("(", ", ", ")")
    // Lean's A × B × C is A × (B × C): the k-th of n is k-1 steps right, then left (but the last).
    case Tree.Proj(on, k, n)   => expr(on) + ".2" * (k - 1) + (if k == n then "" else ".1")
    case Tree.SomeT(a)         => p(s"some ${expr(a)}")
    case Tree.Inj(l, a)        => p(s"${if l then "Except.error" else "Except.ok"} ${expr(a)}")
    case Tree.ListT(es)        => es.map(expr).mkString("[", ", ", "]")
    case Tree.Over(kind, on, b, body) =>
      lazy val r = expr(on)
      // A binder must not capture a variable of the receiver: `∀ x ∈ r, b` puts `r` in scope of `x`.
      val x = unique(b, Names.ident(b.hint), free(r))
      names(b) = x
      val tb = expr(body)
      kind match
        case Iter.All       => p(s"∀ $x ∈ $r, $tb")
        case Iter.Some      => p(s"∃ $x ∈ $r, $tb")
        case Iter.Filter    => p(s"List.filter (fun $x => decide $tb) $r")
        case Iter.FilterNot => p(s"List.filter (fun $x => decide (¬$tb)) $r")
        case Iter.Find      => p(s"List.find? (fun $x => decide $tb) $r")
        case Iter.OptAll    => p(s"∀ $x, $r = some $x → $tb")
        case Iter.OptSome   => p(s"∃ $x, $r = some $x ∧ $tb")
    case Tree.Op(op, args)     => prim(op, args)
    case Tree.Do(steps)        => "do\n" + block(steps, "    ").mkString("\n")
    case Tree.RunOn(call, w, None) => world = true; val c = expr(call); p(s"FrFlow.runOn $c ${expr(w)}")
    // A flow that may fail runs in `ExceptT E (StateM World)`: its outcome, and the world after.
    case Tree.RunOn(call, w, Some(e)) => world = true; val te = tpe(e); val c = expr(call); p(s"FrFlow.runOnE (ε := $te) $c ${expr(w)}")
    case Tree.Part(w, m)       => world = true; s"${expr(w)}.${m.field}"

  /** A flow's steps as the lines of a `do` block, indented by `ind`. */
  def block(s: Steps, ind: String): List[String] = s match
    case c if Steps.reading(c).isDefined => block(concurrent(c), ind)
    // Bound as a whole (`let x ← do …`): the branches' own block is not merged into this one.
    case Steps.Seq(c, b, rest) if Steps.reading(c).isDefined =>
      val r = concurrent(c)
      (s"${ind}let ${if b.wildcard then "_" else local(b)} ← do" :: block(r, ind + "  ")) ++ block(rest, ind)
    case Steps.Ret(t)            => List(s"${ind}pure ${expr(t)}")
    // `(a *> b) *> c` is `a *> (b *> c)` (associativity): one block, not a `do` inside one. Names are unique, so
    // the inner block's names stay its own.
    case Steps.Seq(Steps.Seq(a, b1, r1), b, rest) if b.wildcard => block(Steps.Seq(a, b1, Steps.Seq(r1, b, rest)), ind)
    case Steps.Seq(Steps.Let(b1, v, r1), b, rest) if b.wildcard => block(Steps.Let(b1, v, Steps.Seq(r1, b, rest)), ind)
    case Steps.Seq(first, b, rest) =>
      val bound = if b.wildcard then None else Some(local(b))
      val lines = (bound, first) match
        // A loop or a branch whose result is dropped is a statement of the block itself.
        case (None, Steps.Loop(_, _, _) | Steps.Branch(_, _, _)) => block(first, ind)
        case (None, Steps.Seq(_, _, _) | Steps.Let(_, _, _))     => s"${ind}do" :: block(first, ind + "  ")
        case (Some(n), Steps.Seq(_, _, _) | Steps.Let(_, _, _) | Steps.Loop(_, _, _) | Steps.Branch(_, _, _)) =>
          s"${ind}let $n ← do" :: block(first, ind + "  ")
        // A traverse or a fold opens a `do` of its own, after its binding.
        case (Some(n), Steps.Collect(_, _, _) | Steps.Accumulate(_, _, _, _, _)) => over(first, s"let $n ← ", ind)
        case (None, Steps.Collect(_, _, _) | Steps.Accumulate(_, _, _, _, _))    => over(first, "let _ ← ", ind)
        // An `attempt` whose outcome is dropped gives an `Except`, not nothing: bound to `_`.
        case (None, c @ Steps.Catch(Steps.Seq(_, a, _), e, _, Steps.Ret(Tree.Inj(true, _)))) =>
          tryCatch(c, s"let ${unique(c, "outcome")} : Except ${tpe(e)} ${tpe(a.tpe)} ← ", ind)
        case (None, c @ Steps.Catch(_, _, _, _))                => tryCatch(c, "", ind)
        case (Some(n), c @ Steps.Catch(_, _, _, _))             => tryCatch(c, s"let $n ← ", ind)
        case (None, one)                                         => List(ind + step(one))
        case (Some(n), one)                                      => List(s"${ind}let $n ← ${step(one)}")
      lines ++ block(rest, ind)
    case Steps.Loop(xs, b, body) =>
      val r = expr(xs)
      s"${ind}for ${local(b)} in $r do" :: block(body, ind + "  ")
    case Steps.Branch(c, a, b)   => (s"${ind}if ${expr(c)} then" :: block(a, ind + "  ")) ++ (s"${ind}else" :: block(b, ind + "  "))
    case Steps.Let(b, v, rest)   =>
      val tv = expr(v)
      s"${ind}let ${local(b)} := $tv" :: block(rest, ind)
    case Steps.Collect(_, _, _) | Steps.Accumulate(_, _, _, _, _) => over(s, "", ind)
    case c @ Steps.Catch(_, _, _, _) => tryCatch(c, "", ind)
    case one                     => List(ind + step(one))

  /** A step of flows at once, checked and its commutation recorded; what Lean reads of it, one step at a time. */
  private def concurrent(s: Steps): Steps =
    def total(branch: Steps, what: String) = if Steps.mayFail(branch) then
      fail(s"a branch of $what in proven code may fail: handle its errors inside it (`attempt`, `handleErrorWith`), so that one branch failing never cancels the other halfway")
    def occurring(before: List[(Binder, String)], lines: List[String]) =
      before.filter((_, n) => lines.exists(l => !free(l)(n))).map((b, n) => n -> tpe(b.tpe))
    s match
      case Steps.Par(l, a, r, b) =>
        total(l, "parTupled"); total(r, "parTupled")
        val before = names.toList
        val (an, bn) = (local(a), local(b))
        val (ls, rs) = (block(l, "  "), block(r, "  "))
        val first = (s"let $an ← do" :: ls) ++ (s"let $bn ← do" :: rs) :+ s"pure ($an, $bn)"
        val second = (s"let $bn ← do" :: rs) ++ (s"let $an ← do" :: ls) :+ s"pure ($an, $bn)"
        commutes += Commute("parTupled", occurring(before, first), Nil, first, second, s"(${tpe(a.tpe)} × ${tpe(b.tpe)})")
      case Steps.ParEach(xs, b, body, _, out) =>
        total(body, "parTraverse")
        val before = names.toList.filterNot(_._1 eq b)
        val in = expr(xs)
        val base = Names.ident(b.hint).stripPrefix("«").stripSuffix("»")
        val (x1, x2) = (unique(new Object, s"${base}_one"), unique(new Object, s"${base}_two"))
        val (r1, r2) = (unique(new Object, "one"), unique(new Object, "two"))
        names(b) = x1
        val b1 = block(body, "  ")
        names(b) = x2
        val b2 = block(body, "  ")
        names.remove(b)
        val first = (s"let $r1 ← do" :: b1) ++ (s"let $r2 ← do" :: b2) :+ s"pure ($r1, $r2)"
        val second = (s"let $r2 ← do" :: b2) ++ (s"let $r1 ← do" :: b1) :+ s"pure ($r1, $r2)"
        val elem = tpe(b.tpe)
        commutes += Commute("parTraverse", occurring(before, in :: first) ++ List(x1 -> elem, x2 -> elem),
          List(s"$x1 ∈ $in", s"$x2 ∈ $in", s"$x1 ≠ $x2"), first, second, s"(${tpe(out)} × ${tpe(out)})")
      case Steps.Race(l, r, _) =>
        def timer(x: Steps) = Steps.boundaries(x).forall(_ eq Clock.boundary) && !Steps.effectful(x)
        def sleeps(x: Steps) = Steps.fold(x, false)((acc, y) => acc || PartialFunction.cond(y) {
          case Steps.Op(c, m, _) => (c eq Clock.boundary) && m.getName == "sleep" })
        def transaction(x: Steps) = PartialFunction.cond(x) { case Steps.Atomic(body) => !sleeps(body) }
        if !(timer(l) || transaction(l)) || !(timer(r) || transaction(r)) || (transaction(l) && transaction(r)) then
          fail("a race in proven code is between a timer (a flow of the clock only) and one transaction (`atomically`, which sleeps not), or two timers: a cancelled side must leave nothing, or all of itself")
      case _ => ()
    Steps.sequential(s)

  /** `tryCatchThe E (do …) (fun e => do …)`, after `lead` (a binding, or none): the handler on the line below. */
  private def tryCatch(c: Steps.Catch, lead: String, ind: String): List[String] =
    def closed(ls: List[String]) = ls.init :+ (ls.last + ")")
    val te = tpe(c.err)
    errors += te
    val body = block(c.body, ind + "    ")
    val handler = s"$ind  (fun ${if c.b.wildcard then "_" else local(c.b)} => do" :: block(c.handler, ind + "    ")
    (s"$ind${lead}tryCatchThe $te (do" :: closed(body)) ++ closed(handler)

  /** `xs.mapM fun x => do …` and `xs.foldlM (init := z) fun acc x => do …`, after `lead` (a binding, or none). */
  private def over(s: Steps, lead: String, ind: String): List[String] = s match
    case Steps.Collect(xs, b, body) =>
      val r = expr(xs)
      s"$ind$lead$r.mapM fun ${local(b)} => do" :: block(body, ind + "  ")
    case Steps.Accumulate(xs, z, acc, b, body) =>
      val r = expr(xs)
      val tz = expr(z)
      s"$ind$lead$r.foldlM (init := $tz) fun ${local(acc)} ${local(b)} => do" :: block(body, ind + "  ")
    case other => block(other, ind)

  /** One step, on a line of its own. */
  private def step(s: Steps): String = s match
    case Steps.Ret(t)              => s"pure ${expr(t)}"
    case Steps.Op(b, m, args)      => boundaries += b; (s"${b.lean}.${Names.ident(m.getName)}" :: args.map(expr)).mkString(" ")
    case Steps.Read(_)             => "get"
    case Steps.Write(_, t)         => s"set ${expr(t)}"
    case Steps.Modify(_, b, body)  =>
      val n = local(b)
      s"modify (fun $n => ${expr(body)})"
    case Steps.Raise(e, t)         => val te = tpe(t); errors += te; s"throwThe $te ${expr(e)}"
    case Steps.Outside(_)          => fail("a step of the outside world (Flow.effect) in a flow Lean proves: only a production implementation of a boundary takes one")
    case other                     => block(other, "").mkString("; ")

  private def free(r: => String)(x: String): Boolean =
    !(s"(?<![\\w'.])${java.util.regex.Pattern.quote(x)}(?![\\w'])").r.findFirstIn(r).isDefined

  private def caseDef(c: Arm): String =
    val pat = c.pat match
      case Pat.Ctor(adt, ctor, bs) =>
        val args = bs.map(b => if b.wildcard then "_" else local(b))
        types.declare(adt)
        if ctor.singleton.isDefined && adt.isEnum then ctor.lean else (ctor.lean :: args).mkString(" ")
      case Pat.SomeP(b)    => s"some ${if b.wildcard then "_" else local(b)}"
      case Pat.NoneP       => "none"
      case Pat.InjP(l, b)  => s"${if l then "Except.error" else "Except.ok"} ${if b.wildcard then "_" else local(b)}"
      case Pat.ConsP(h, t) =>
        val (a, b) = (if h.wildcard then "_" else local(h), if t.wildcard then "_" else local(t))
        s"$a :: $b"
      case Pat.NilP        => "[]"
    s"| $pat => ${expr(c.body)}"

  private def paramRef(prm: Param[?]): String =
    val n = Names.ident(prm.name)
    if !paramRefs.contains(n) then
      paramRefs(n) = tpe(prm.termType)
      paramObjects += prm
    n

  private def prim(op: Prim, args: List[Tree]): String =
    def e(t: Tree) = expr(t)
    lazy val r = e(args.head)
    def arg = e(args(1))
    def bin(sym: String) = { val x = r; p(s"$x $sym $arg") }
    def fresh(base: String) = unique(new Object, base, free(r))
    op match
      case Prim.Eq        => bin("=")
      case Prim.Ne        => bin("≠")
      case Prim.And       => bin("∧")
      case Prim.Or        => bin("∨")
      case Prim.Not       => p(s"¬${negated(r)}")
      case Prim.Implies   => val l = negated(r); p(s"$l → $arg")
      case Prim.Add       => bin("+")
      case Prim.Sub       => bin("-")
      case Prim.Mul       => bin("*")
      case Prim.Div       => val x = r; p(s"Int.tdiv $x $arg")
      case Prim.Mod       => val x = r; p(s"Int.tmod $x $arg")
      case Prim.Lt        => bin("<")
      case Prim.Le        => bin("≤")
      case Prim.Gt        => bin(">")
      case Prim.Ge        => bin("≥")
      case Prim.Max       => val x = r; p(s"max $x $arg")
      case Prim.Min       => val x = r; p(s"min $x $arg")
      case Prim.Neg       => p(s"-$r")
      case Prim.Concat    => bin("++")
      case Prim.Cons      => val x = r; p(s"$x :: $arg")
      case Prim.Append    => bin("++")
      case Prim.Contains  => val x = arg; p(s"$x ∈ $r")
      case Prim.IsEmpty   => p(s"$r = []")
      case Prim.NonEmpty  => p(s"$r ≠ []")
      case Prim.Length    => p(s"($r).length : Int")
      case Prim.MapL      => val f = r; p(s"List.map $f $arg")
      case Prim.FlatMap   => val f = r; p(s"List.flatMap $f $arg")
      case Prim.FoldLeft  => val f = r; val z = arg; p(s"List.foldl $f $z ${e(args(2))}")
      case Prim.HeadOption => p(s"List.head? $r")
      case Prim.ToSet     => val y = fresh("y"); p(s"fun $y => $y ∈ $r")
      case Prim.Take      => val n = r; p(s"List.take (Int.toNat $n) $arg")
      case Prim.Drop      => val n = r; p(s"List.drop (Int.toNat $n) $arg")
      case Prim.Zip       => val x = r; p(s"List.zip $x $arg")
      case Prim.Get       => val x = r; p(s"$x $arg")
      case Prim.HasKey    => val x = r; p(s"$x $arg ≠ none")
      case Prim.GetOrElse => val x = r; val k = arg; p(s"Option.getD ($x $k) ${e(args(2))}")
      case Prim.Updated   => val k = fresh("k"); val key = arg; p(s"fun $k => if $k = $key then some ${e(args(2))} else $r $k")
      case Prim.Removed   => val k = fresh("k"); p(s"fun $k => if $k = $arg then none else $r $k")
      case Prim.SetHas    => val x = r; p(s"$x $arg")
      case Prim.Incl      => val y = fresh("y"); p(s"fun $y => $y = $arg ∨ $r $y")
      case Prim.Excl      => val y = fresh("y"); p(s"fun $y => $y ≠ $arg ∧ $r $y")
      case Prim.Union     => val y = fresh("y"); p(s"fun $y => $r $y ∨ $arg $y")
      case Prim.Intersect => val y = fresh("y"); p(s"fun $y => $r $y ∧ $arg $y")
      case Prim.SubsetOf  => val y = fresh("y"); p(s"∀ $y, $r $y → $arg $y")
      case Prim.OptContains => val x = r; p(s"$x = some $arg")
      case Prim.IsDefined => p(s"$r ≠ none")
      case Prim.OptIsEmpty => p(s"$r = none")
      case Prim.OptGetOrElse => val x = r; p(s"Option.getD $x $arg")

  /** A Scala value as Lean writes it: what the macro made of the same value written in a model. */
  def value(v: Any, t: LeanType[?]): String = t.shape match
    case Shape.Prop   => if v.asInstanceOf[Boolean] then "True" else "False"
    case Shape.Num(_) =>
      val n = v match { case i: Int => BigInt(i); case l: Long => BigInt(l); case b: BigInt => b; case o => fail(s"$o is not a number") }
      if n < 0 then p(n.toString) else n.toString
    case Shape.Str    => Names.string(v.asInstanceOf[String])
    case Shape.UnitT  => "()"
    case Shape.ListOf(a) => v.asInstanceOf[List[?]].map(value(_, a)).mkString("[", ", ", "]")
    case Shape.OptionOf(a) => v match
      case Some(x) => p(s"some ${value(x, a)}")
      case _       => "none"
    case Shape.EitherOf(e, a) => v match
      case Left(x)  => p(s"Except.error ${value(x, e)}")
      case Right(x) => p(s"Except.ok ${value(x, a)}")
      case _        => fail(s"$v is not an outcome")
    case Shape.TupleOf(as) => v.asInstanceOf[Product].productIterator.toList.zip(as).map(value).mkString("(", ", ", ")")
    case Shape.MapOf(kt, vt) =>
      val m = v.asInstanceOf[Map[Any, Any]]
      if m.isEmpty then "(fun _ => none)"
      else
        val k = unique(new Object, "k")
        p(s"fun $k => " + m.toList.map((a, b) => (value(a, kt), value(b, vt))).foldRight("none")((kv, rest) => s"if $k = ${kv._1} then some ${kv._2} else $rest"))
    case Shape.SetOf(a) =>
      val s = v.asInstanceOf[Set[Any]]
      if s.isEmpty then "(fun _ => False)"
      else
        val y = unique(new Object, "y")
        p(s"fun $y => " + (s.toList.map(x => s"$y = ${value(x, a)}") :+ "False").mkString(" ∨ "))
    case Shape.Data(adt) =>
      val c = adt.ctorOf(v)
      types.declare(adt)
      if adt.isEnum && c.singleton.isDefined then c.lean
      else p((c.lean :: v.asInstanceOf[Product].productIterator.toList.zip(c.fields.map(_._2)).map(value)).mkString(" "))
    case other => fail(s"Lean has no value for $v (${Types.scala(t)})")
