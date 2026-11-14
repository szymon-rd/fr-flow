package frflow.dsl.compiled.source

import frflow.core.threads.Datum
import frflow.core.threads.Datum.{Many, Text}
import frflow.dsl.lifted.NotRead

/** A type as the tree read holds it (`FrFlow/Scala/Tree.v`, `ty`): one constructor for each form of type the
  * compiler's reader gives, and a refusal of any other, so that none is passed over.
  */
private[source] trait SourceTypes extends SourceSyms:
  import q.reflect.*

  def ty(t: TypeRepr): Datum = t match
    case NoPrefix()               => Datum.of("TyNone")
    case t: TermRef               => Datum.of("TyTerm", sym(t.termSymbol))
    case t: TypeRef               => named(t)
    case AppliedType(c, args)     => Datum.of("TyApp", ty(c), Many(args.map(ty)))
    case ConstantType(c)          => Datum.of("TyConst", const(c))
    case ThisType(of)             => Datum.of("TyThis", Text(scopeKey(of.typeSymbol)))
    case SuperType(self, parent)  => Datum.of("TySuper", ty(self), ty(parent))
    case ByNameType(u)            => Datum.of("TyByName", ty(u))
    case AndType(a, b)            => Datum.of("TyAnd", ty(a), ty(b))
    case OrType(a, b)             => Datum.of("TyOr", ty(a), ty(b))
    case AnnotatedType(u, annot)  => Datum.of("TyAnnot", ty(u), Text(annot.tpe.typeSymbol.fullName))
    case Refinement(p, name, i)   => Datum.of("TyRefine", ty(p), Text(name), ty(i))
    case TypeBounds(lo, hi)       => Datum.of("TyBounds", ty(lo), ty(hi))
    case other                    => binding(other)

  /** The forms that bind parameters, or refer to them. */
  private def binding(t: TypeRepr): Datum = t match
    case t: TypeLambda            => Datum.of("TyLambda", Datum.texts(t.paramNames), ty(t.resType))
    case ParamRef(binder, i)      => Datum.of("TyParamRef", Text(parameter(binder, i)))
    case MethodType(ns, ts, res)  => Datum.of("TyMethod", Datum.texts(ns), Many(ts.map(ty)), ty(res))
    case PolyType(ns, _, res)     => Datum.of("TyPoly", Datum.texts(ns), ty(res))
    case MatchType(b, s, cases)   => Datum.of("TyMatch", ty(b), ty(s), Many(cases.map(ty)))
    case MatchCase(p, r)          => Datum.of("TyCase", ty(p), ty(r))
    case RecursiveType(u)         => Datum.of("TyRec", ty(u))
    case RecursiveThis(_)         => Datum.of("TyRecThis")
    case other                    => throw NotRead(s"FrFlow: a type of a form the tree has no constructor for: " +
      s"${other.show} (${other.getClass.getSimpleName})")

  private def parameter(binder: TypeRepr, i: Int): String = binder match
    case b: LambdaType => b.paramNames(i)
    case _             => s"_$i"

  /** A class is its key, whatever path reaches it; a type member declared by a package or an object is its
    * full name, and with it the type it is another name of, if it is one; a type parameter is named with what
    * declares it; any other is a member of its prefix.
    */
  private def named(t: TypeRef): Datum =
    val s = t.typeSymbol
    if s.isNoSymbol then Datum.of("TySelect", ty(t.qualifier), Text(t.name))
    else if s.isTypeParam then Datum.of("TyParam", Text(scopeKey(s.maybeOwner)), Text(s.name))
    else if s.isClassDef then Datum.of("TyRef", Text(classKey(s)))
    else if fixed(s.maybeOwner) then alias(t).fold(Datum.of("TyRef", Text(s.fullName)))(is =>
      Datum.of("TyAlias", Text(s.fullName), ty(is)))
    else Datum.of("TySelect", ty(t.qualifier), Text(t.name))

  /** What `t` is another name of: nothing of a type that is abstract, or opaque. */
  private def alias(t: TypeRef): Option[TypeRepr] =
    val s = t.typeSymbol
    Option.when(s.isAliasType && !s.flags.is(Flags.Opaque))(t.dealias).filter:
      case to: TypeRef => to.typeSymbol != s
      case _           => true

  private def fixed(owner: Symbol): Boolean = owner.isPackageDef || owner.flags.is(Flags.Module)
