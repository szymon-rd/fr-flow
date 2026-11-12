package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Decl, Param, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.known.Thrown

/** A call, by what is called: `throw`; a local method; a field read through a method; a definition of the unit;
  * an inline method, which is its body (`ReadInline`); a method of the JDK, which is its operation (`ReadOps`);
  * a constructor; a method of Scala's library that `Lang.v` has (`ReadData`); a closure applied; a method of a
  * class not read, which is `extern`. A call of anything else is not read.
  */
private[threads] trait ReadCalls extends ReadExprs:
  import q.reflect.*

  /** A closure given as an argument: a `code` (`ReadClosures`). */
  def closureArg(arg: Term)(using Env): Res
  /** A call of a local method (`ReadVars`). */
  def local(c: Call, slot: Slot.Method)(using Env): Res

  def inlined(c: Call)(using Env): Option[Res]
  def op(c: Call)(using Env): Option[Res]
  def data(c: Call)(using Env): Option[Res]

  def call(c: Call)(using env: Env): Res = env.vars.get(c.symbol) match
    case Some(m: Slot.Method) => local(c, m)
    case _                    =>
      thrown(c).orElse(got(c)).orElse(defined(c)).orElse(inlined(c)).orElse(op(c)).orElse(built(c)).orElse(data(c))
        .orElse(invoked(c)).orElse(extern(c)).getOrElse(refuse(s"a call of ${c.symbol.fullName}"))

  private def thrown(c: Call)(using Env): Option[Res] = (c.fn, c.args) match
    case (Ident("throw"), List(e)) if c.symbol.owner.name.startsWith("<") =>
      val v = value(coerce(expr(e), Ty.Exn))
      Some(Res(v.steps, Rocq.of("throw", v.term), Ty.Never, Res.Kind.Program))
    case _                                                                 => None

  /** A method with no argument that reads a field: of `this`, of an object of the unit, of an exception caught. */
  private def got(c: Call)(using env: Env): Option[Res] = c.on.filter(_ => c.args.isEmpty).flatMap {
    case This(_)   => env.self.filter(_ => sigFor(c.symbol, None).isEmpty).flatMap(_.fields.get(c.name))
    case id: Ident if env.caught.contains((id.symbol, c.name)) =>
      Some(Res.value(Rocq.Ref(env.caught((id.symbol, c.name))), Ty.Exn))
    case qual      => Option.when(sigFor(c.symbol, onType(qual)).isEmpty)(projected(qual, c.name)).flatten }

  private def onType(qual: Term): Option[String] = reprOf(qual).collect { case Ty.Named(n) => n }

  /** The arguments of a call, each at its parameter's type; one whose parameter takes a closure is one. */
  def arguments(args: List[Term], params: List[Ty])(using Env): List[Res] =
    if args.size != params.size then refuse(s"${args.size} arguments where ${params.size} are taken")
    else args.zip(params).map((a, ty) => if ty == Ty.Code then closureArg(a) else coerce(expr(a), ty))

  /** A call of a definition of the unit: its name applied, `this` first. */
  private def defined(c: Call)(using Env): Option[Res] =
    sigFor(c.symbol, c.on.flatMap(onType)).map { sig =>
      val self = sig.on.toList.map(t => coerce(expr(c.on.getOrElse(refuse("a method called on nothing"))),
        Ty.Named(t)))
      applied(sig.name, self ++ arguments(c.args, sig.params.map(_.ty)), sig.result, Res.Kind.Program) }

  /** An object made: an exception; an object of a class of the unit from its fields (a case class's `apply`), or
    * a case of a sum from its parameters; of a class not read, `extern`.
    */
  private def built(c: Call)(using env: Env): Option[Res] =
    val made = c.fn match
      case Select(New(tpt), _)                               => Some(plain(tpt.tpe).typeSymbol)
      case _ if c.name == "apply" && c.symbol.owner.flags.is(Flags.Module) => Some(c.symbol.owner.companionClass)
      case _                                                 => None
    made.filter(_.isClassDef).flatMap(cls => env.vars.get(cls) match
      case Some(Slot.Thunk(tree, at)) => Some(expr(tree)(using at))
      case _ if isThrowable(cls)      => Some(Res.value(exception(cls, c.args), Ty.Exn))
      case _ if isOpaque(cls)         => Some(externally(s"${cls.fullName}.apply", c.args, Ty.Nat))
      case _                          => fromFields(cls, c.args))

  private def fromFields(cls: Symbol, args: List[Term])(using Env): Option[Res] =
    val inline = sums.flatMap(s => s.cases.filter(_.sym == cls).flatMap(k => k.fields.map(fs =>
      (k.ctor, fs.map(_._2), Ty.Named(s.name))))).headOption
    val whole = records.find(_.sym == cls).map(r => (Decl.maker(r.name), r.fields.map(_._2), Ty.Named(r.name)))
    inline.orElse(whole).map((ctor, fields, ty) =>
      applied(ctor, arguments(args, fields.map(_.ty)), ty, Res.Kind.Value))

  /** An exception made: its constructor of `exn`. Its arguments (a message) are not read. */
  private def exception(cls: Symbol, args: List[Term])(using Env): Rocq =
    unread(cls.fullName, args)
    thrownAs(cls).fold(Rocq.of(Thrown.Other, Rocq.Text(cls.fullName)))(t =>
      if t.fields.isEmpty then Rocq.Ref(t.ctor) else refuse(s"an exception of ${cls.fullName} made"))

  def thrownAs(cls: Symbol): Option[Thrown] = Thrown.classes.get(cls.fullName)

  /** The arguments of a call that is not read are not read; one that is an effect of the code read is refused. */
  private def unread(name: String, args: List[Term])(using Env): Unit =
    args.foreach(a => scala.util.Try(expr(a)).toOption.filter(r => !r.isValue || r.steps.nonEmpty)
      .foreach(_ => refuse(s"an effect in an argument of $name, which is not read")))

  /** A call of code that is not read, taken to touch nothing of the JDK's state here: `extern`. */
  private def externally(name: String, args: List[Term], gives: Ty)(using Env): Res =
    unread(name, args)
    Res.program(Rocq.of("extern", Rocq.Text(name)), gives)

  /** A closure applied: `invoke`, with the one argument held as a `val`, or `VUnit`. */
  private def invoked(c: Call)(using Env): Option[Res] = c.on.filter(q => c.name == "apply" && isFunction(plain(q.tpe)))
    .map { f =>
      val arg = c.args match
        case Nil       => Res.value(Rocq.Ref("VUnit"), Ty.Val)
        case List(one) => coerce(expr(one), Ty.Val)
        case _         => refuse("a closure of several arguments")
      applied("invoke", List(coerce(expr(f), Ty.Code), arg), Ty.Val, Res.Kind.Program) }

  /** A method of a class not read: a definition named for it, which is `extern` (`ReadClasses.externs`). */
  private def extern(c: Call)(using Env): Option[Res] =
    c.on.filter(q => isOpaque(plain(q.tpe).typeSymbol)).map { on =>
      val params: List[Param] = paramsOf(c.symbol)
      val gives = repr(c.symbol.tree.asInstanceOf[DefDef].returnTpt.tpe)
      applied(externName(c.symbol), coerce(expr(on), Ty.Nat) :: arguments(c.args, params.map(_.ty)), gives,
        Res.Kind.Program) }

  def externName(m: Symbol): String = s"${m.owner.name}_${m.name}"
