package frflow.dsl.term

import cats.data.NonEmptyList
import frflow.core.name.TypeName
import frflow.core.term.{Constructor, Selector as FieldSelector}
import scala.deriving.Mirror
import scala.quoted.*

/** The derivation, at compile time, of what a domain type is to the term language: its `LeanType` (a case class's
  * fields, or an enum's cases, from its `Mirror`), a field's typed selector (Scala's own getter and `copy`), and a
  * constructor as a curried function. Nothing is written per type, and nothing is cast.
  */
object DataMacros:
  def derived[T: Type](using Quotes): Expr[LeanType[T]] =
    import quotes.reflect.*
    Expr.summon[Mirror.Of[T]] match
      case Some('{ $m: Mirror.ProductOf[T] }) =>
        '{ Data.product[T](${ Expr(Type.show[T]) }, ${ fields[T] },
          args => $m.fromProduct(Tuple.fromArray(args.toArray))) }
      case Some('{ $m: Mirror.SumOf[T] { type MirroredElemTypes = es; type MirroredElemLabels = ls } }) =>
        val alts = cases[T, es, ls]
        '{ Data.sum[T](${ Expr(Type.show[T]) }, NonEmptyList.fromListUnsafe($alts), (a: Any) => a match
          case t: T => $m.ordinal(t)
          case _    => -1) }
      case _ => report.errorAndAbort(s"${Type.show[T]} is not a case class or an enum")

  /** A case class's fields, each a selector with its `LeanType`. */
  def fields[T: Type](using Quotes): Expr[List[LeanType.Field[T, ?]]] =
    import quotes.reflect.*
    val cls = TypeRepr.of[T].typeSymbol
    Expr.ofList(cls.caseFields.zipWithIndex.map((f, i) => field[T](f.name, i)))

  /** One field's selector with its `LeanType` (a compile error if it has none). */
  def field[T: Type](name: String, i: Int)(using Quotes): Expr[LeanType.Field[T, ?]] =
    import quotes.reflect.*
    TypeRepr.of[T].memberType(TypeRepr.of[T].typeSymbol.fieldMember(name)).asType match
      case '[f] => typedField[T, f](name, i)

  /** The same, typed by the field's own type `F`. */
  def typedField[T: Type, F: Type](name: String, i: Int)(using Quotes): Expr[LeanType.Field[T, F]] =
    import quotes.reflect.*
    val all = TypeRepr.of[T].typeSymbol.caseFields
    val t = Expr.summon[LeanType[F]].getOrElse(report.errorAndAbort(s"no LeanType for field $name: ${Type.show[F]}"))
    def copied(r: Expr[T], v: Expr[F]): Expr[T] =
      Apply(Select.unique(r.asTerm, "copy"), all.map(g => if g.name == name then v.asTerm else Select(r.asTerm, g)))
        .asExprOf[T]
    '{ LeanType.Field(FieldSelector[T, F](${ Expr(name) }, ${ Expr(i) }, TypeName(${ Expr(names[T]._1) }), $t.ty,
      (r: T) => ${ Select.unique('r.asTerm, name).asExprOf[F] }, (r: T, v: F) => ${ copied('r, 'v) }), $t) }

  /** An enum's cases: each one's name, fields and maker. */
  private def cases[T: Type, es: Type, ls: Type](using Quotes): Expr[List[Data.Alt[T]]] =
    (Type.of[es], Type.of[ls]) match
      case ('[c *: cs], '[l *: rest]) =>
        val label = Type.valueOfConstant[l].fold("?")(_.toString)
        '{ ${ alt[T, c](label) } :: ${ cases[T, cs, rest] } }
      case _ => '{ Nil }

  private def alt[T: Type, C: Type](label: String)(using Quotes): Expr[Data.Alt[T]] =
    import quotes.reflect.*
    Expr.summon[Mirror.ProductOf[C]] match
      case Some(m) =>
        val fs = fieldsOf[C].map((n, t) => t.asType match
          case '[f] => '{ (${ Expr(n) }, ${ Expr.summon[LeanType[f]].getOrElse(report.errorAndAbort(
            s"no LeanType for field $n")) }: LeanType[?]) })
        '{ (${ Expr(label) }, ${ Expr.ofList(fs) }, (args: List[Any]) => ${ upcast[C, T]('{ $m.fromProduct(
          Tuple.fromArray(args.toArray)) }) }) }
      case None => report.errorAndAbort(s"case $label of ${Type.show[T]} has no Mirror")

  private def upcast[C: Type, T: Type](c: Expr[C])(using Quotes): Expr[T] =
    import quotes.reflect.*
    Typed(c.asTerm, TypeTree.of[T]).asExprOf[T]

  /** `C`'s constructor as a curried function of its fields (`f1 => f2 => W`, `W` the type it is a value of: `C`, or
    * the enum it is a case of), or the value itself if it has none.
    */
  def constructor[C: Type, W: Type](using Quotes): Expr[Constructor[?]] =
    import quotes.reflect.*
    val (data, ctor) = names[C]
    def fnType(rest: List[(String, TypeRepr)]): TypeRepr = rest match
      case Nil            => TypeRepr.of[W]
      case (_, t) :: more => TypeRepr.of[Function1].appliedTo(List(t, fnType(more)))
    def curried(rest: List[(String, TypeRepr)], done: List[Term], owner: Symbol): Term = rest match
      case Nil            => Typed(made[C](done.reverse.map(_.asExprOf[Any])).asTerm, TypeTree.of[W])
      case (n, t) :: more =>
        Lambda(owner, MethodType(List(n))(_ => List(t), _ => fnType(more)), (o, ps) =>
          curried(more, ps.collect { case p: Term => p }.take(1) ++ done, o).changeOwner(o))
    val fs = fieldsOf[C]
    fnType(fs).asType match
      case '[f] =>
        val make = curried(fs, Nil, Symbol.spliceOwner).asExprOf[f]
        '{ Constructor[f](TypeName(${ Expr(data) }), frflow.core.name.CtorName(${ Expr(ctor) }), $make) }

  /** A value of `C` from its fields' values, by its `Mirror`. */
  private def made[C: Type](args: List[Expr[Any]])(using Quotes): Expr[C] =
    import quotes.reflect.*
    Expr.summon[Mirror.ProductOf[C]].fold(report.errorAndAbort(s"${Type.show[C]} has no Mirror"))(m =>
      '{ $m.fromProduct(Tuple.fromArray(${ Expr.ofList(args) }.toArray)) })

  /** The enum `C` is a case of, if it is one. */
  def sumOf[C: Type](using Quotes): Option[quotes.reflect.TypeRepr] =
    import quotes.reflect.*
    val tpe = TypeRepr.of[C]
    tpe.widen.baseClasses.drop(if tpe.isSingleton then 0 else 1).find(_.flags.is(Flags.Enum)).map(_.typeRef)

  /** `C`'s fields, by name and type; none for a singleton case. */
  def fieldsOf[C: Type](using Quotes): List[(String, quotes.reflect.TypeRepr)] =
    import quotes.reflect.*
    if TypeRepr.of[C].isSingleton then Nil
    else TypeRepr.of[C].typeSymbol.caseFields.map(f => f.name -> TypeRepr.of[C].memberType(f))

  /** The Lean type and constructor names of `C`: `Booking.mk` for a case class, `Event.Expired` for an enum's case. */
  def names[C: Type](using Quotes): (String, String) =
    import quotes.reflect.*
    val tpe = TypeRepr.of[C]
    sumOf[C].fold((tpe.typeSymbol.name, "mk"))(e =>
      (e.typeSymbol.name, if tpe.isSingleton then tpe.termSymbol.name else tpe.typeSymbol.name))
