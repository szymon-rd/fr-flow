package frflow.dsl.compiled.effect

import frflow.core.effect.{ClassName, Effect, EType, FieldName, FieldOf, MethodName, MethodOf, Pure}
import frflow.core.effect.Tree as Emitted

/** The classes of the files read, each with its fields and its methods' trees. A class's constructor is a
  * method, `new`, called on the object just made: it writes what the class is given into its fields, then runs
  * the class's body in order, a field's value written where the field is declared.
  */
private[effect] trait EmitClasses extends EmitCalls:
  import q.reflect.*

  /** The classes a file declares, in order. Anything else it declares is refused. */
  def declared(t: Tree): List[ClassDef] = t match
    case PackageClause(_, stats)                  => stats.flatMap(declared)
    case c: ClassDef if plainClass(c)             =>
      if c.symbol.flags.is(Flags.Final) then List(c) else refuse("a class another may extend", c)
    case _: Import | _: Export                    => Nil
    case other                                    => refuse("what is no class with a body of its own", other)

  private def plainClass(c: ClassDef): Boolean =
    val flags = c.symbol.flags
    !flags.is(Flags.Trait) && !flags.is(Flags.Module) && !flags.is(Flags.Abstract) &&
      c.constructor.leadingTypeParams.isEmpty &&
      c.parents.forall(p => p.symbol.owner == defn.ObjectClass || p.symbol == defn.ObjectClass)

  /** The names of a class, its fields and its methods: said of every class before any body is read. */
  def name(c: ClassDef): Unit =
    val cls = ClassName(c.name)
    if classes.values.exists(_ == cls) then refuse(s"a second class named ${c.name}", c)
    classes(c.symbol) = cls
    methods(c.constructor.symbol) = MethodName(cls, "new")
    c.body.foreach:
      case v: ValDef if unread(v.symbol) => refuse("a field evaluated when or where it is read", v)
      case v: ValDef                     =>
        fields(v.symbol) = FieldOf(FieldName(cls, v.name), ty(v.tpt.tpe, v))
        constant(v).foreach(constants(v.symbol) = _)
      case d: DefDef if d.symbol.flags.is(Flags.FieldAccessor) => ()
      case d: DefDef if unread(d.symbol) => refuse("a method Scala puts in place where it is called", d)
      case d: DefDef                     => methods(d.symbol) = MethodName(cls, unshared(cls, d.name))
      case _                             => ()

  /** What has no value or tree of its own where it is declared: `lazy` or `inline`. */
  private def unread(s: Symbol): Boolean = s.flags.is(Flags.Lazy) || s.flags.is(Flags.Inline)

  /** What a `final val` of a literal's type is: Scala reads it as the literal, also before the field is written. */
  private def constant(v: ValDef): Option[Pure] = v.tpt.tpe match
    case ConstantType(c) if v.symbol.flags.is(Flags.Final) => Some(literal(c, v))
    case _                                                 => None

  /** A method's name in its class: the first of a name has it, the next ones are numbered. */
  private def unshared(cls: ClassName, name: String): String =
    val taken = methods.values.filter(_.cls == cls).map(_.name).toSet
    (name #:: LazyList.from(2).map(i => s"${name}_$i")).find(!taken(_)).get

  def trees(c: ClassDef): List[MethodOf] =
    constructor(c) :: c.body.collect { case d: DefDef if methods.contains(d.symbol) => method(d) }

  private def inputs(d: DefDef, fresh: Fresh): List[(Symbol, String, EType)] =
    if d.leadingTypeParams.nonEmpty then refuse("a method that takes types", d)
    d.termParamss.flatMap(_.params).map(p => (p.symbol, fresh(p.name), ty(p.tpt.tpe, p)))

  /** The place a method's body is read in: `this`, and what the method is given. */
  private def entered(d: DefDef): (Env, List[(String, EType)]) =
    val fresh = Fresh()
    val self = fresh("this")
    val given_ = inputs(d, fresh)
    (Env(Pure.Local(self), given_.map((s, x, _) => s -> Pure.Local(x)).toMap, Set.empty, fresh),
      (self -> EType.Ref) :: given_.map((_, x, t) => x -> t))

  private def method(d: DefDef): MethodOf =
    val (env, takes) = entered(d)
    val body = d.rhs.getOrElse(refuse("a method with no body", d))
    val tree = Emitted.simplified(expr(body, env)((p, _) => Emitted.Give(p)))
    MethodOf(methods(d.symbol), takes, ty(d.returnTpt.tpe, d), tree)

  private def constructor(c: ClassDef): MethodOf =
    val (env, takes) = entered(c.constructor)
    val given_ = c.constructor.termParamss.flatMap(_.params).map(p => p.name -> env.values(p.symbol)).toMap
    def from(stats: List[Statement]): Emitted = stats match
      case Nil                                           => Emitted.Give(Pure.Nothing)
      case (v: ValDef) :: rest if v.rhs.isEmpty          => given_.get(v.name).fold(from(rest))(x =>
        Emitted.Do(None, Effect.Put(env.self, fields(v.symbol).name, x), from(rest)))
      case (v @ ValDef(_, _, Some(rhs))) :: rest         => expr(rhs, env)((p, _) =>
        Emitted.Do(None, Effect.Put(env.self, fields(v.symbol).name, p), from(rest)))
      case (t: Term) :: rest                             => expr(t, env.dropping)((_, _) => from(rest))
      case (_: DefDef) :: rest                           => from(rest)
      case other :: _                                    => refuse("a class's member that is no field or method", other)
    MethodOf(methods(c.constructor.symbol), takes, EType.Unit, Emitted.simplified(from(c.body)))
