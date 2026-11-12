package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Decl, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.known.Jdk

/** An expression's value: a literal, a variable in scope, a field, an object, a call (`ReadCalls`), or a construct
  * read as one program (`tail`). What the compiler expanded while typing (`summon`) is its expansion. An effect
  * inside an expression is run before the statement it is in, what it gives named (`Reading.values`). An
  * expression that assigns a `var` is read only where a statement is.
  */
private[threads] trait ReadExprs extends Coercions:
  import q.reflect.*

  /** A method applied: what is called (a `Select` or an `Ident`), its arguments, every list's in order, and its
    * type arguments.
    */
  final case class Call(fn: Term, args: List[Term], types: List[TypeRepr]):
    def symbol: Symbol = fn.symbol
    def name: String = fn.symbol.name
    def on: Option[Term] = fn match
      case Select(qual, _) => Some(qual)
      case _               => None

  def callOf(t: Term): Option[Call] = t match
    case Apply(f, args)                                => callOf(f).map(c => c.copy(args = c.args ++ args))
    case TypeApply(f, types)                           => callOf(f).map(_.copy(types = types.map(_.tpe)))
    case s: Select if s.symbol.isDefDef                => Some(Call(s, Nil, Nil))
    case i: Ident if i.symbol.isDefDef                 => Some(Call(i, Nil, Nil))
    case _                                             => None

  /** A call read (`ReadCalls`). */
  def call(c: Call)(using Env): Res
  /** The `var`s in scope that `t` assigns, in the order they are declared (`ReadVars`). */
  def assigned(t: Tree)(using Env): List[Symbol]
  /** The statements of a block that ends in `last`, and the scope after them (`ReadBlocks`). */
  def statements(stats: List[Statement], last: Term)(using Env): (List[Step], Env)
  /** Whether `t` returns from the method it is in (`ReadVars`). */
  def returns(t: Tree): Boolean

  def expr(t: Term)(using env: Env): Res =
    if assigned(t).nonEmpty then refuse("an expression that assigns a variable, where its value is used")
    else read(t)

  private def read(t: Term)(using env: Env): Res = t match
    case Typed(e, _)                                   => read(e)
    case Inlined(_, Nil, e)                            => read(e)
    case Inlined(_, bindings, e)                       => flat(bindings, e, t)
    case Literal(c)                                    => literal(c)
    case Block(Nil, last)                              => read(last)
    case Block(stats, last)                            => flat(stats, last, t)
    case If(_, _, _) | Match(_, _) | Try(_, _, _)      => whole(t)
    case This(_)                                       => env.self.fold(refuse("`this` outside a class"))(_.value)
    case _ if callOf(t).nonEmpty                       => callOf(t).fold(refuse("a call"))(call)
    case id: Ident                                     => variable(id)
    case sel: Select                                   => selected(sel)
    case other                                         => refuse(s"the expression ${other.show}")

  /** A construct read as one program. */
  private def whole(t: Term)(using Env): Res =
    if returns(t) then refuse("a return where a value is used")
    val done = tail(t, Goal.Value)
    Res.program(done.term, done.ty)

  /** A block's statements, then its value; as one program where a name of its own would hide one in scope. */
  private def flat(stats: List[Statement], last: Term, whole: Term)(using env: Env): Res =
    val (steps, inner) = statements(stats, last)
    if steps.flatMap(_.bound).exists(env.locals.contains) then this.whole(whole)
    else
      val r = read(last)(using inner)
      r.copy(steps = steps ++ r.steps)

  private def literal(c: Constant): Res = c match
    case BooleanConstant(b) => Res.value(Rocq.Ref(b.toString), Ty.Bool)
    case UnitConstant()     => Res.value(Rocq.unit, Ty.Unit)
    case IntConstant(n)     => Res.value(Rocq.Num(BigInt(n)), Ty.Z)
    case NullConstant()     => Res.value(Rocq.At("None", Ty.Never), Ty.option(Ty.Never))
    case _                  => refuse(s"the constant ${c.show}")

  private def variable(id: Ident)(using env: Env): Res = env.vars.get(id.symbol) match
    case Some(Slot.Local(name, ty))                => Res.value(Rocq.Ref(name), ty)
    case Some(Slot.Mutable(name, ty, None))        => Res.value(Rocq.Ref(name), ty)
    case Some(Slot.Mutable(_, Ty.Of(_, of), Some(known))) => Res.value(Rocq.Ref(known), of)
    case Some(Slot.ByName(name))                   =>
      Res.program(Rocq.of("invoke", Rocq.Ref(name), Rocq.Ref("VUnit")), Ty.Val)
    case Some(Slot.Thunk(tree, at))                => expr(tree)(using at)
    case Some(Slot.Tested(option, content, _))     => Res.value(Rocq.Ref(option), Ty.option(content))
    case Some(_)                                   => refuse(s"the name ${id.name}, read as a value")
    case None                                      => field(id.symbol).getOrElse(static(id))

  /** A field of `this`, named without it. */
  private def field(sym: Symbol)(using env: Env): Option[Res] =
    env.self.filter(_.cls == sym.owner).flatMap(_.fields.get(sym.name))

  private def selected(sel: Select)(using env: Env): Res = sel.qualifier match
    case This(_) if field(sel.symbol).nonEmpty => field(sel.symbol).getOrElse(refuse(sel.name))
    case qual                                  => projected(qual, sel.name).getOrElse(static(sel))

  /** A field of an object of a class of the unit: `C_f x`. */
  def projected(qual: Term, name: String)(using Env): Option[Res] =
    reprOf(qual).collect { case Ty.Named(c) => c }.flatMap(record).flatMap(r =>
      r.fields.map(_._2).find(_.name == name).map { f =>
        val on = value(coerce(expr(qual), Ty.Named(r.name)))
        Res(on.steps, Rocq.of(Decl.projection(r.name, name), on.term), f.ty, Res.Kind.Value) })

  /** The type `t`'s value is read at, if its Scala type is one that is read. */
  def reprOf(t: Term): Option[Ty] = scala.util.Try(repr(t.tpe)).toOption

  /** An object, or a top-level value: a case of a sum; a handle, if it is of the JDK or of a class not read; an
    * object of `obj` otherwise; `Nil` and `None`.
    */
  private def static(t: Term): Res =
    val sym = t.symbol
    def isObject = sym.flags.is(Flags.Module) || sym.flags.is(Flags.Enum)
    sums.flatMap(_.cases).find(c => sym.flags.is(Flags.Module) && c.sym == sym.moduleClass) match
      case Some(c)                                  => Res.value(Rocq.Ref(c.ctor), Ty.Named(typeNames(sumOf(c))))
      case None if sym.fullName.endsWith(".Nil")    => Res.value(Rocq.At("nil", Ty.Never), Ty.list(Ty.Never))
      case None if sym.fullName == "scala.None"     => Res.value(Rocq.At("None", Ty.Never), Ty.option(Ty.Never))
      case None if isGlobal(t)                      =>
        Res.value(Rocq.Ref(catalogue.global(sym.name, plain(t.tpe).typeSymbol.fullName)), Ty.Nat)
      case None if isObject                         =>
        Res.value(Rocq.of("VObj", Rocq.Ref(catalogue.singleton(sym.owner.name.stripSuffix("$"), sym.name))), Ty.Val)
      case None                                     => refuse(s"the value ${sym.fullName}")

  /** A top-level value that is a handle: of a class not read, or of one whose objects need not be made. Its
    * initialiser is not read.
    */
  private def isGlobal(t: Term): Boolean =
    val cls = plain(t.tpe).typeSymbol
    val owner = t.symbol.owner
    t.symbol.isValDef && (owner.flags.is(Flags.Module) || owner.isPackageDef) &&
      (isOpaque(cls) || bases(cls).exists(b => Jdk.ambient(b.fullName)))

  private def sumOf(c: Case): Symbol = sums.find(_.cases.contains(c)).fold(c.sym)(_.sym)

  /** The object of `obj` an expression names, if it names one: its owner and its name. */
  def singleton(t: Term): Option[(String, String)] = t match
    case Typed(e, _)                                              => singleton(e)
    case _: Ident | _: Select if (t.symbol.flags.is(Flags.Module) || t.symbol.flags.is(Flags.Enum)) &&
        reprOf(t).isEmpty                                         =>
      Some((t.symbol.owner.name.stripSuffix("$"), t.symbol.name))
    case _                                                        => None
