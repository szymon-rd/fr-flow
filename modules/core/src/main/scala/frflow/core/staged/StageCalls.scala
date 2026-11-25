package frflow.core.staged

import frflow.core.code.Datum
import frflow.core.effect.Idents

/** A call staged (`Meaning.applied_step`, `select_with`, `ident_with`, `construct`): what a member is, and which
  * arguments it takes unevaluated, is read of the table here.
  */
private[staged] trait StageCalls extends StageExprs:
  import Tree.*

  def applied(f: Tree, targs: List[Datum], args: List[Given])(using Env): P = f match
    case Apply(g, more)        => applied(g, targs, more.map(Right(_)) ++ args)
    case TypeApply(g, ts)      => applied(g, ts, args)
    case Select(New(ty), ctor) => construct(ty, ctor, targs, args)
    case Select(on, s)         => select(expr(on), s, targs, args)
    case Ident(s)              => ident(s, targs, args)
    case Typed(g, _)           => applied(g, targs, args)
    case _                     => P.Stuck("a call of what is neither a name nor a member")

  /** The arguments of a call in order (`Meaning.eval_args`): one taken unevaluated is kept for later. */
  def evaluated(lazily: List[Boolean], args: List[Given])(next: List[V] => P)(using Env): P = args match
    case Nil       => next(Nil)
    case a :: rest =>
      val more = (v: V) => evaluated(lazily.drop(1), rest)(vs => next(v :: vs))
      (lazily.headOption.contains(true), a) match
        case (true, Right(t)) => more(byName(t))
        case (true, Left(_))  => refuse("a value given where an argument is taken unevaluated")
        case (_, Right(t))    => bind(expr(t), "arg")(more)
        case (_, Left(v))     => more(v)

  private def takenByName(d: DefDef): List[Boolean] = Defined.params(d).map(Defined.byName)

  def select(on: P, s: Sym, targs: List[Datum], args: List[Given])(using Env): P = s match
    case Sym.Member(owner, name, _) => table.kindOf(s) match
      case Kind.Method(d) => bind(on, "on")(v => evaluated(takenByName(d), args)(vs => called(s, v, vs)))
      case Kind.Field     => bind(on, "on")(v => op("get_field", value(v), Arg.Text(name)))
      case Kind.Lazy      => bind(on, "on")(v => called(s, v, Nil))
      case Kind.Module(c) => op("module_obj", Arg.Text(c))
      case Kind.Inner     => P.Stuck(s"an object declared in a class, one for each object of the class: $name")
      case Kind.Outside   => universal(owner -> name)(on, targs, args).getOrElse(bind(on, "on")(v =>
        if table.implementedSomewhere(s) then evaluated(Nil, args) { vs =>
          calling(s, Nil)
          op("own", Arg.Name(s), value(v), Arg.Types(targs), Arg.Vals(vs))
        }
        else outside(s, v, targs, args)))
    case _                          => P.Stuck("a member that is no member")

  private def called(s: Sym, on: V, args: List[V]): P = op("call_method", Arg.Name(s), value(on), Arg.Vals(args))

  def ident(s: Sym, targs: List[Datum], args: List[Given])(using e: Env): P = s match
    case Sym.Local(_, _) if args.isEmpty => read(s.key)
    case Sym.Local(_, _)                 => local(s.key, args)
    case Sym.Member(owner, name, _)      => table.kindOf(s) match
      case Kind.Module(c) => op("module_obj", Arg.Text(c))
      case Kind.Outside   =>
        universal(owner -> name)(P.Stuck("nothing to compare"), targs, args)
          .getOrElse(outside(s, V.Unit, targs, args))
      case _              => select(thisOf(owner), s, targs, args)
    case Sym.NoSym                       => P.Stuck("a name that names nothing")

  /** A function made in the code, called (`Meaning.call_local`). */
  private def local(key: String, args: List[Given])(using e: Env): P = e.bound.get(key) match
    case Some(Bound.Made(f, d)) => evaluated(takenByName(d), args)(vs => op("apply_", value(f), Arg.Vals(vs)))
    case Some(_)                => P.Stuck(s"a call of what is no function: $key")
    case None                   => e.rest.fold(P.Stuck(s"a function that is not in scope: $key"))(sc =>
      evaluated(Nil, args)(vs => op("call_sought", variable(sc), Arg.Text(key), Arg.Vals(vs))))

  /** What is said of every value, and so is no method of a class (`Meaning.universal`). */
  private def universal(member: (String, String))(on: P, targs: List[Datum], args: List[Given])(using Env)
      : Option[P] =
    val (owner, name) = member
    val two = (compare: String) => bind(on, "left")(v => evaluated(Nil, args) {
      case List(w) => op(compare, value(v), value(w))
      case _       => P.Stuck(s"a comparison with other than one argument: $name")
    })
    val typed = (test: String, otherwise: V => P) => bind(on, "on")(v => targs match
      case List(t) => op(test, value(v), Arg.Type(t))
      case _       => otherwise(v))
    if !Set("scala.Any", "java.lang.Object", "scala.AnyRef")(owner) then None
    else name match
      case "=="                              => Some(two("eq_"))
      case "!="                              => Some(two("ne_"))
      case "eq"                              => Some(two("same_"))
      case "isInstanceOf"                    =>
        Some(typed("is_instance", _ => P.Stuck("isInstanceOf with other than one type")))
      case "asInstanceOf" | "$asInstanceOf$" => Some(typed("as_instance", P.Give(_)))
      case _                                 => None

  /** The members of Scala's library that take an argument unevaluated (`Library.pure`): `&&`, `||`, and what an
    * option or an either falls back to. That the library says the same of every definition the code calls is
    * checked where the staged code is (`Staged.takes`).
    */
  private def lazily(owner: String, name: String): List[Boolean] =
    val option = Set("scala.Option", "scala.Some", "scala.None$")(owner) && Set("getOrElse", "orElse", "fold")(name)
    val either = Set("scala.util.Either", "scala.util.Left", "scala.util.Right",
      "scala.util.Either$.LeftProjection")(owner) && name == "getOrElse"
    val boolean = owner == "scala.Boolean" && (name == "&&" || name == "||")
    if option || either || boolean then List(true) else Nil

  /** A definition from outside is called: noted, with the arguments it is taken to take unevaluated. */
  private def calling(s: Sym, taken: List[Boolean]): Unit = { val _ = called += (s -> taken) }

  /** A definition from outside called (`Meaning.call_outside`). */
  def outside(s: Sym, on: V, targs: List[Datum], args: List[Given])(using Env): P = s match
    case Sym.Member(owner, name, _) if lazily(owner, name).nonEmpty =>
      calling(s, lazily(owner, name))
      val given_ = args.zipWithIndex.map {
        case (Right(t), i) if lazily(owner, name).lift(i).contains(true) => Left(byName(t))
        case (Right(t), _)                                               => Right(expr(t))
        case (Left(v), _)                                                => Right(P.Give(v))
      }
      op("out_lazy", Arg.Name(s), value(on), Arg.Types(targs), Arg.Lazily(given_))
    case Sym.Member(_, _, _) =>
      calling(s, Nil)
      evaluated(Nil, args)(vs => op("out", Arg.Name(s), value(on), Arg.Types(targs), Arg.Vals(vs)))
    case _                   => P.Stuck("a definition from outside that is no member")

  /** An object made (`Meaning.construct`). One of a class written inside a method keeps the variables in scope. */
  private def construct(ty: Datum, ctor: Sym, targs: List[Datum], args: List[Given])(using e: Env): P =
    Defined.tyClass(ty) match
      case None      => P.Stuck("an object made of a type that is no class")
      case Some(cls) => table.classOf(cls) match
        case Some(c) =>
          val taken = c.ctor match
            case d: DefDef => takenByName(d)
            case _         => Nil
          val kept = if cls.contains('#') then e.kept else Kept(Nil, None)
          evaluated(taken, args)(vs => op("construct_", Arg.Text(cls), Arg.Scope(kept), Arg.Vals(vs)))
        case None    =>
          val signature = ctor match
            case Sym.Member(_, _, sig) => sig
            case _                     => "()"
          outside(Sym.Member(cls, "<init>", signature), V.Unit, targs, args)

  /** A function made in the code, as a value: its definition, the name of its unit in the place of its body,
    * with what it keeps. Its body is that unit.
    */
  def function(d: DefDef, group: List[DefDef])(using e: Env): V =
    d.rhs.foreach { body =>
      val names = Names()
      val params = Defined.params(d).map(p => (p, names.fresh(p.s.key.takeWhile(_ != '#'))))
      val siblings = group.map(g =>
        g.s.key -> Bound.Made(V.Function(Defined.stub(g.data, unitOf(g)), Kept(Nil, Some("sc"))), g))
      val inner = e.inside("sc", names).havingAll(siblings).havingAll(params.map(given_))
      val program = P.Given(params.map(_._2), expr(body)(using inner))
      nested += StagedUnit(UnitKind.Function(unitOf(d)), s"fn_${Idents.plain(d.s.key)}_${numbered()}", program)
    }
    V.Function(Defined.stub(d.data, unitOf(d)), e.kept)

  /** The unit that runs a function made in the code, named by the class the function is written in and by its
    * own name: a name made inside a method is one definition's within its file, and a class is in one file.
    */
  private def unitOf(d: DefDef): Sym.Local = d.s match
    case Sym.Local(name, id) => Sym.Local(s"$within $name", id)
    case other               => Sym.Local(s"$within ${other.key}", 0)

  /** A parameter in the scope of its method's body: one taken unevaluated is read through what holds it. */
  def given_(p: ValDef, x: String): (String, Bound) =
    p.s.key -> (if Defined.byName(p) then Bound.Held(V.Var(x)) else Bound.Plain(V.Var(x)))

  /** An argument taken unevaluated, as a value: a unit of its own, with what it keeps. */
  def byName(t: Tree)(using e: Env): V =
    val n = numbered()
    val unit = Sym.Local("<by-name>", n)
    nested += StagedUnit(UnitKind.ByName(unit), s"by_name_$n", expr(t)(using e.inside("sc", Names())))
    V.ByName(unit, e.kept)
