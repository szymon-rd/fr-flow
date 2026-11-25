package frflow.dsl.compiled.normal

import frflow.core.effect.{ClassName, EType, FieldName, FieldOf, MethodName}
import frflow.core.normal.{Atom, Local, NormalMethod, Stmt}

/** The classes of the files read, each with its fields and its methods. A class's constructor is a method,
  * `new`, called on the object just made: it writes what the class is given into its fields, then runs the
  * class's body in order, a field's value written where the field is declared.
  */
private[normal] trait ReadClasses extends ReadCalls:
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
  private def constant(v: ValDef): Option[Atom] = v.tpt.tpe match
    case ConstantType(c) if v.symbol.flags.is(Flags.Final) => Some(literal(c, v))
    case _                                                 => None

  /** A method's name in its class: the first of a name has it, the next ones are numbered. */
  private def unshared(cls: ClassName, name: String): String =
    val taken = methods.values.filter(_.cls == cls).map(_.name).toSet
    (name #:: LazyList.from(2).map(i => s"${name}_$i")).find(!taken(_)).get

  def routines(c: ClassDef): List[NormalMethod] =
    constructor(c) :: c.body.collect { case d: DefDef if methods.contains(d.symbol) => method(d) }

  /** A method's body about to be read: what the method is given, each a local. */
  private def entered(d: DefDef): (Body, List[(Local, EType)]) =
    if d.leadingTypeParams.nonEmpty then refuse("a method that takes types", d)
    val b = Body()
    val params = d.termParamss.flatMap(_.params).map { p =>
      val made = b.local(p.name, ty(p.tpt.tpe, p))
      b.bound(p.symbol) = Atom.Of(made)
      made -> b.types(made)
    }
    (b, params)

  /** A method read whether or not its class gave it a name. */
  def tried(d: DefDef): NormalMethod =
    if !methods.contains(d.symbol) then methods(d.symbol) = MethodName(ClassName(d.symbol.owner.name), d.name)
    method(d)

  private def method(d: DefDef): NormalMethod =
    val (b, params) = entered(d)
    val body = b.block(expr(d.rhs.getOrElse(refuse("a method with no body", d)), Use.Plain)(using b))
    NormalMethod(methods(d.symbol), params, ty(d.returnTpt.tpe, d), body)

  private def constructor(c: ClassDef): NormalMethod =
    val (b, params) = entered(c.constructor)
    given Body = b
    val given_ = c.constructor.termParamss.flatMap(_.params).map(p => p.name -> b.bound(p.symbol)).toMap
    val body = b.block { c.body.foreach(member(_, given_)); Atom.Nothing }
    NormalMethod(methods(c.constructor.symbol), params, EType.Unit, body)

  /** A member in the class's body, as the constructor runs it. */
  private def member(s: Statement, given_ : Map[String, Atom])(using b: Body): Unit = s match
    case v: ValDef if v.rhs.isEmpty  =>
      given_.get(v.name).foreach(x => b.add(Stmt.Write(Atom.Self, fields(v.symbol).name, x)))
    case v @ ValDef(_, _, Some(rhs)) => b.add(Stmt.Write(Atom.Self, fields(v.symbol).name, expr(rhs, Use.Plain)))
    case t: Term                     => expr(t, Use.Dropped): Unit
    case _: DefDef                   => ()
    case other                       => refuse("a class's member that is no field or method", other)
