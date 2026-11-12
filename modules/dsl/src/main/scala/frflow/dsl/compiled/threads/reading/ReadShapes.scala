package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Ctor, Decl, Param, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.known.ThreadUnit.Kind

/** The classes of the unit as types.
  *
  *   - A class is the record of its fields, the constructor's parameters and the `val`s, in order: `Record C :=
  *     mkC { C_f : T }`. One with a field of its own type is an inductive type, `mkC` over the fields, with a
  *     function `C_f` for each.
  *   - A trait is a sum, `S_<case>` for each case: an object is a constant; a class of the unit is held (`(x :
  *     C)`); a trait with parameters holds them, and is read as the sum.
  *   - A trait one class of the unit extends, and no other, is read as that class; a class that extends a class of
  *     the unit as that class.
  */
private[threads] trait ReadShapes extends ReadTypes:
  import q.reflect.*

  /** A class read as a record: its fields, by the symbol of each. */
  final case class Record(sym: Symbol, name: String, fields: List[(Symbol, Param)])

  /** A case of a sum: its constructor and what it holds (`fields`: of a trait with parameters, they). */
  final case class Case(sym: Symbol, ctor: String, fields: Option[List[(Symbol, Param)]])
  final case class Sum(sym: Symbol, name: String, cases: List[Case])

  private def named(name: String): Symbol = Symbol.requiredClass(name)

  private lazy val listed: List[Symbol] = unit.types.map {
    case Kind.Class(n)  => named(n)
    case Kind.Sum(n, _) => named(n) }

  private lazy val caseSymbols: Map[Symbol, List[Symbol]] = unit.types.collect { case Kind.Sum(n, cases) =>
    named(n) -> (if cases.isEmpty then named(n).children.map(c => if c.isClassDef then c else c.moduleClass)
      else cases.map(named)) }.toMap

  lazy val typeNames: Map[Symbol, String] =
    val own = listed.map(s => s -> s.name).toMap
    val inline = caseSymbols.toList.flatMap((sum, cases) =>
      cases.filterNot(c => own.contains(c) || c.flags.is(Flags.Module)).map(_ -> sum.name))
    own ++ inline ++ extended(own ++ inline)

  /** The traits a class of the unit extends that are no type of the unit's, the JDK's or Scala's, each with the
    * one class that extends it.
    */
  private def extended(known: Map[Symbol, String]): Map[Symbol, String] =
    val classes = unit.types.collect { case Kind.Class(n) => named(n) }
    def outside(b: Symbol): Boolean = known.contains(b) || b.fullName.startsWith("java.") ||
      b.fullName.startsWith("scala.") || bases(b).exists(known.contains)
    classes.flatMap(c => bases(c).filterNot(outside).map(_ -> c.name)).groupMap(_._1)(_._2)
      .collect { case (b, List(one)) => b -> one }

  private def fieldsOf(cls: Symbol): List[(Symbol, Param)] = cls.tree match
    case ClassDef(_, _, _, _, body) => body.collect { case v: ValDef if !v.symbol.flags.is(Flags.Lazy) =>
      v.symbol -> Param(v.name, repr(v.tpt.tpe)) }
    case _                          => Nil

  lazy val records: List[Record] = unit.types.collect { case Kind.Class(n) =>
    Record(named(n), named(n).name, fieldsOf(named(n))) }

  lazy val sums: List[Sum] = caseSymbols.toList.map((sum, cases) => Sum(sum, sum.name, cases.map(caseOf(sum, _))))

  private def caseOf(sum: Symbol, c: Symbol): Case =
    val ctor = s"${sum.name}_${c.name.stripSuffix("$")}"
    if c.flags.is(Flags.Module) || records.exists(_.sym == c) then Case(c, ctor, None)
    else Case(c, ctor, Some(fieldsOf(c)))

  def record(name: String): Option[Record] = records.find(_.name == name)
  def sum(name: String): Option[Sum] = sums.find(_.name == name)

  /** The case of a sum that holds the class read as `ty`. */
  def caseHolding(ty: String): Option[(Sum, Case)] =
    sums.flatMap(s => s.cases.filter(c => c.fields.isEmpty && typeNames.get(c.sym).contains(ty)).map(s -> _))
      .headOption

  /** The type declarations, in the order the unit lists them. */
  def declared: List[Decl] = listed.flatMap(sym => record(sym.name).map(recordDecl).orElse(
    sum(sym.name).map(s => List(Decl.Inductive(s.name, s.cases.map(ctorOf))))).getOrElse(Nil))

  private def ctorOf(c: Case): Ctor = c.fields match
    case Some(fields)                         => Ctor(c.ctor, fields.map(_._2))
    case None if c.sym.flags.is(Flags.Module) => Ctor(c.ctor, Nil)
    case None                                 => Ctor(c.ctor, List(Param("x", Ty.Named(typeNames(c.sym)))))

  private def recordDecl(r: Record): List[Decl] =
    val fields = r.fields.map(_._2)
    if !fields.exists(_.ty.names.contains(r.name)) then List(Decl.Record(r.name, fields))
    else Decl.Inductive(r.name, List(Ctor(Decl.maker(r.name), fields))) :: fields.indices.toList.map(i =>
      Decl.Definition(Decl.projection(r.name, fields(i).name), List(Param("x", Ty.Named(r.name))), fields(i).ty,
        Rocq.Unpack(fields.indices.toList.map(j => if j == i then "a" else "_"), Rocq.Ref("x"), Rocq.Ref("a"))))

  /** The cases of `obj` a caller's data may hold: the classes of the unit that are public. */
  def shared: List[Ctor] = listed.filter(s => !s.flags.is(Flags.Private) && s.privateWithin.isEmpty)
    .map(s => Catalogue.obj(s.name))
