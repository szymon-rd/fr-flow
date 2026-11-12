package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Param, Ty}
import frflow.dsl.compiled.threads.known.ThreadUnit.Member
import frflow.dsl.lifted.NotRead

/** The definitions of the unit, by name, before any body is read: what a call of one is written as.
  *
  *   - Method `m` of a class read as `C` is `C_m (this : C) …`; of an object `O`, `O_m …`; a top-level method keeps
  *     its name. The constructor of `C` is `C_new`. Of the methods of one name an owner declares in its source,
  *     each is numbered in order: `m_1`, `m_2`.
  *   - The parameters are those of every list, in order, `using` ones included; one the source does not name is
  *     `x1`, `x2`, ….
  *   - A method with a parameter or a result of a type that is not read has no definition: a call of it is not
  *     read.
  */
private[threads] trait ReadSigs extends ReadShapes:
  import q.reflect.*

  /** A definition of the unit: the method read, its name, the name its closures are named after, the class `this`
    * is read as, its parameters and the type of what it gives.
    */
  final case class Sig(sym: Symbol, name: String, base: String, on: Option[String], params: List[Param],
      result: Ty)

  /** What a definition is read from. */
  enum Entry:
    case Method(sig: Sig)
    case Constructor(sig: Sig, record: Record)
    case Dispatch(sig: Sig, sum: Sum)

    def sig: Sig

  /** The definitions of each group, in the order of the source. */
  lazy val entries: List[(String, List[Entry])] = unit.groups.map(g => g.title -> g.members.flatMap(read))
  lazy val sigs: List[Sig] = entries.flatMap(_._2).map(_.sig)

  def defined(name: String): Boolean = sigs.exists(_.name == name) || catalogue.names(name)

  /** The definition a call of `m` on a value read as `on` is a call of: `m`'s, or that of the method of `on` that
    * implements it.
    */
  def sigFor(m: Symbol, on: Option[String]): Option[Sig] = sigs.find(_.sym == m).orElse(
    sigs.find(s => s.on.nonEmpty && s.on == on && s.sym.allOverriddenSymbols.contains(m)))

  private def read(member: Member): List[Entry] = member match
    case Member.Whole(owner)        =>
      val cls = Symbol.requiredClass(owner)
      record(cls.name).map(r => Entry.Constructor(constructor(r), r)).toList ++ written(cls).flatMap(method)
    case Member.Object(owner)       => written(Symbol.requiredModule(owner).moduleClass).flatMap(method)
    case Member.Of(owner, name)     => owners(Symbol.requiredClass(owner)).flatMap(written).filter(_.name == name)
      .flatMap(method)
    case Member.TopLevel(pkg, name) => topLevels(pkg).flatMap(written).filter(_.name == name).flatMap(method)
    case Member.Dispatch(name)      => sums.filter(_.sym.fullName == name).flatMap(s => s.sym.declarations.filter(d =>
      d.isDefDef && d.flags.is(Flags.Deferred) && !made(d)).map(d => Entry.Dispatch(sigOf(d), s)))

  /** A class and its companion. */
  private def owners(cls: Symbol): List[Symbol] =
    cls :: List(cls.companionModule).filterNot(_.isNoSymbol).map(_.moduleClass)

  /** The objects that hold a package's top-level definitions, one for each source file. */
  private def topLevels(pkg: String): List[Symbol] =
    Symbol.requiredPackage(pkg).declarations.filter(d => d.isClassDef && d.name.endsWith("$package$"))

  /** The methods `owner` declares in its source, with a body. */
  private def written(owner: Symbol): List[Symbol] = owner.declarations.filter(d =>
    d.isDefDef && !d.isClassConstructor && !d.flags.is(Flags.Synthetic) && !d.flags.is(Flags.Deferred))

  /** A method's name as the source has it: a top-level one without the object of its file. */
  def displayName(m: Symbol): String = m.fullName.replaceAll("""[^.]+\$package\$?\.""", "")

  /** The definition of a method; one whose parameters or result are of a type that is not read has none. */
  private def method(m: Symbol): Option[Entry] =
    try Some(Entry.Method(sigOf(m)))
    catch case refusal: NotRead =>
      catalogue.refused(displayName(m), refusal.getMessage)
      None

  private def sigOf(m: Symbol): Sig =
    val (prefix, on) = unitType(m.owner) match
      case Some(t) if !m.owner.flags.is(Flags.Module) => (t + "_", Some(t))
      case _ if m.owner.name.endsWith("$package$")    => ("", None)
      case _                                          => (m.owner.name.stripSuffix("$") + "_", None)
    val alike = written(m.owner).filter(_.name == m.name)
    val numbered = if alike.size > 1 then s"_${alike.indexOf(m) + 1}" else ""
    Sig(m, prefix + m.name + numbered, prefix + m.name, on, paramsOf(m), resultOf(m))

  /** The type of what a method gives, as its definition declares it. */
  def resultOf(m: Symbol): Ty = m.tree match
    case d: DefDef => repr(d.returnTpt.tpe)
    case _         => refuse(s"the method ${m.fullName}, whose definition is not read")

  private def constructor(r: Record): Sig =
    Sig(r.sym.primaryConstructor, s"${r.name}_new", s"${r.name}_new", None, paramsOf(r.sym.primaryConstructor),
      Ty.Named(r.name))

  /** The parameters of a method, of every list, as its definition declares them. */
  def declaredParams(m: Symbol): List[ValDef] = m.tree match
    case d: DefDef => d.termParamss.flatMap(_.params)
    case _         => refuse(s"the method ${m.fullName}, whose definition is not read")

  def paramsOf(m: Symbol): List[Param] =
    val all = declaredParams(m)
    val unnamed = all.filter(p => made(p.symbol))
    all.map(p => Param(if made(p.symbol) then s"x${unnamed.indexOf(p) + 1}" else p.name, reprOfParam(p.tpt.tpe)))
