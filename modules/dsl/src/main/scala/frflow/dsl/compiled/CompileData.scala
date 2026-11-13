package frflow.dsl.compiled

import frflow.core.code.DataRep
import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.{Constructor, Selector as FieldSelector}
import frflow.core.ty.Ty
import frflow.dsl.term.RocqType
import frflow.dsl.term.Term as DTerm

/** The developer's data the compiler reads: a case class made, a field read, a copy with fields replaced, an
  * enum's case. A case class is a record of the term language; an enum, a sum. What Scala builds and takes apart
  * of a type's values is what its spec says (`DataRep`): the compiler makes no value itself.
  */
private[compiled] trait CompileData extends Compiling:
  this: Compiler =>
  import q.reflect.*

  /** `C(…)` or `new C(…)` of a case class `C` with no type parameters: the compiler's own `apply` and the class's
    * first constructor only (an `apply` the developer wrote is a method, read as one).
    */
  def record(c: Calling)(using Env): Option[DTerm[Any]] =
    val cls = c.on match
      case New(tpt) if c.name == "<init>" && c.whole.symbol == tpt.tpe.typeSymbol.primaryConstructor =>
        tpt.tpe.typeSymbol
      case on if c.name == "apply" && c.whole.symbol.flags.is(Flags.Synthetic)                       =>
        on.tpe.termSymbol.companionClass
      case _                                                                                         =>
        Symbol.noSymbol
    Option.when(isRecord(cls)) {
      val fields = fieldsOf(cls.typeRef)
      if fields.size != c.args.size then
        refuse(s"${cls.name} made from ${c.args.size} of its ${fields.size} fields", c.whole)
      make(cls.typeRef, c.args.zip(fields).map((a, f) => read(a, f._2)), c.whole)
    }

  private def isRecord(cls: Symbol): Boolean =
    !cls.isNoSymbol && cls.flags.is(Flags.Case) && cls.typeRef.typeArgs.isEmpty && cls.typeMembers.forall(m =>
      !m.isTypeParam)

  def caseValue(t: Term): DTerm[Any] = make(t.symbol.termRef, Nil, t)

  /** The enum a case is of, if it is one. */
  private def sumOf(of: TypeRepr): Option[TypeRepr] =
    of.widen.baseClasses.drop(if of.isSingleton then 0 else 1).find(_.flags.is(Flags.Enum)).map(_.typeRef)

  /** A value of a case class, or of an enum's case, made from its fields' terms: the type's constructor as a
    * function term (`f1 => f2 => W`, `W` the class or the enum), applied to each.
    */
  private def make(of: TypeRepr, given_ : List[DTerm[Any]], at: Tree): DTerm[Any] =
    val made = shape(of, at)
    val parts = made.parts.map(_._2)
    def curried(left: Int, got: List[Any]): Any =
      if left == 0 then made.rep.make(made.ctor, got) else (x: Any) => curried(left - 1, got :+ x)
    val types = parts.scanRight(made.whole)((a, r) => RocqType.fn(using a, r).asInstanceOf[RocqType[Any]])
    given_.zip(types.drop(1)).foldLeft(DTerm.construct[Any](Constructor(made.data, made.ctor,
      curried(parts.size, Nil)))(using types.head))((f, a) =>
      DTerm.app[Any, Any](madeFunction(f), a._1)(using a._2))

  /** A case class, or an enum's case, as its spec has it: the type it is a value of (the class, or the enum),
    * its constructor there, what makes and takes apart a value (`DataRep`), and its fields' names and types.
    */
  private final case class Shape(whole: RocqType[Any], data: TypeName, ctor: CtorName, rep: DataRep,
      parts: List[(String, RocqType[Any])])

  private def shape(of: TypeRepr, at: Tree): Shape =
    val whole = spec(sumOf(of).getOrElse(of), at)
    val (data, ctor) = whole.ty match
      case Ty.Data(name) => (name, CtorName(sumOf(of).fold("mk")(_ =>
        if of.isSingleton then of.termSymbol.name else of.typeSymbol.name)))
      case other         => refuse(s"a value of ${of.show}, which is no data ($other)", at)
    val rep = whole.declares.types.get(data).flatMap(_.headOption).fold(refuse(s"a value of ${of.show}, whose " +
      "type is not declared by its spec", at))(_.rep)
    Shape(whole, data, ctor, rep,
      (if of.isSingleton then Nil else fieldsOf(of)).map(f => (f._1, spec(f._2, at): RocqType[Any])))

  /** An enum's case, for a match's arm and a field read of it: its label, each field's selector (read off the
    * value, replaced by making the case again), and what tells a value of the enum is this case.
    */
  final case class CaseOf(label: String, fields: List[RocqType.Field[Any, Any]], told: Any => Option[Any])

  def caseOf(of: TypeRepr, at: Tree): CaseOf =
    val made = shape(of, at)
    def parts(value: Any): List[Any] = made.rep.split(value)._2
    val fields = made.parts.zipWithIndex.map { case ((name, t), i) =>
      RocqType.Field[Any, Any](FieldSelector[Any, Any](name, i, made.data, t.ty, parts(_)(i), (value, x) =>
        made.rep.make(made.ctor, parts(value).updated(i, x))), t)
    }
    CaseOf(made.ctor.value, fields, value => Option.when(made.rep.split(value)._1 == made.ctor)(value))

  def field(c: Calling)(using Env): Option[DTerm[Any]] =
    val own = c.on.tpe.widen
    val i = fieldsOf(own).indexWhere(_._1 == c.name)
    if c.name == "copy" && isRecord(own.typeSymbol) && c.whole.symbol.flags.is(Flags.Synthetic) then
      Some(copied(c, own))
    else Option.when(c.args.isEmpty && i >= 0 && own.typeSymbol.flags.is(Flags.Case))(
      DTerm.select(read(c.on, own), fieldAt(own, i, c.whole)))

  /** The selector of a case class's field, as its spec has it. */
  private def fieldAt(own: TypeRepr, i: Int, at: Tree): RocqType.Field[Any, Any] =
    val fields = if sumOf(own).nonEmpty then caseOf(own, at).fields else spec(own, at).fields
    fields.lift(i).fold(refuse(s"a field of ${own.show}, whose spec has none", at))(
      _.asInstanceOf[RocqType.Field[Any, Any]])

  /** `b.copy(end = e)`: each field given replaced, in the order given; one left as it is kept. */
  private def copied(c: Calling, own: TypeRepr)(using Env): DTerm[Any] =
    val fields = fieldsOf(own)
    val given_ = c.args.zipWithIndex.map {
      case (NamedArg(name, value), _) => (fields.indexWhere(_._1 == name), value)
      case (value, i)                 => (i, value)
    }.filterNot((_, value) => unchanged(value))
    given_.foldLeft(read(c.on, own)) { case (t, (i, value)) =>
      DTerm.copy(t, fieldAt(own, i, c.whole).selector, read(value, fields(i)._2))
    }
