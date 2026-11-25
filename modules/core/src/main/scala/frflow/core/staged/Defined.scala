package frflow.core.staged

import frflow.core.code.Datum
import frflow.core.code.Datum.{Many, Of, Text}

/** What a member is, where the code names it (`Meaning.kind_of`). */
enum Kind:
  case Method(d: Tree.DefDef)
  case Field
  case Lazy
  case Module(cls: String)
  case Inner
  case Outside

/** What the files read define (`FrFlow/Scala/Table.v`), computed where the code is staged: the same lookups,
  * with the same answers, as the table Rocq builds of the same files.
  */
final class Defined(files: List[Tree]):
  import Tree.*

  private val all: List[Tree] = files.flatMap(Defined.nodes)
  private val classes: Map[String, ClassDef] =
    all.collect { case c: ClassDef => c.name -> c }.reverse.toMap
  private val members: Map[Sym, Tree] = all.collect {
    case v @ ValDef(s: Sym.Member, _, _, _)    => s -> v
    case d @ DefDef(s: Sym.Member, _, _, _, _) => s -> d
  }.reverse.toMap

  /** Every class of the files, in the order read. */
  def everyClass: List[ClassDef] = all.collect { case c: ClassDef => c }.distinctBy(_.name)

  def classOf(name: String): Option[ClassDef] = if Defined.foreign(name) then None else classes.get(name)

  def member(s: Sym): Option[Tree] = s match
    case Sym.Member(owner, _, what) if !Defined.foreign(owner) && what != "package" => members.get(s)
    case _                                                                          => None

  def isModule(c: ClassDef): Boolean = c.flags.contains("Module")

  /** What declares a member is a package or an object. */
  private def static(owner: String): Boolean = classOf(owner).forall(isModule)

  def kindOf(s: Sym): Kind = (member(s), s) match
    case (Some(d: DefDef), _)                                       => Kind.Method(d)
    case (Some(ValDef(_, flags, t, _)), Sym.Member(owner, _, _)) if flags.contains("Module") =>
      Defined.tyClass(t).fold(Kind.Outside)(c => if static(owner) then Kind.Module(c) else Kind.Inner)
    case (Some(ValDef(_, flags, _, _)), _) if flags.contains("Module") => Kind.Outside
    case (Some(ValDef(_, flags, _, _)), _) if flags.contains("Lazy") => Kind.Lazy
    case (Some(_: ValDef), _)                                       => Kind.Field
    case _                                                          => Kind.Outside

  /** A class and what it inherits from, itself first (`Table.own`). */
  def own(cls: String): List[String] =
    if Defined.foreign(cls) || !classes.contains(cls) then List(cls) else lineage(12, cls)

  private def lineage(fuel: Int, cls: String): List[String] = classes.get(cls) match
    case Some(c) if fuel > 0 => (cls :: parentNames(c).reverse.flatMap(lineage(fuel - 1, _))).distinct
    case _                   => List(cls)

  private def parentNames(c: ClassDef): List[String] =
    c.parents.flatMap(p => Defined.made(p).flatMap(Defined.tyClass))

  /** Whether some class of the files gives a body to `s`, declared outside them (`Table.own_impl`). */
  def implementedSomewhere(s: Sym): Boolean = everyClass.exists(_.body.exists {
    case DefDef(own, _, _, Some(_), data) => own == s || Defined.overridden(data).contains(s)
    case _                                => false
  })

object Defined:
  import Tree.*

  private def within(pkg: String, name: String): Boolean = name == pkg || name.startsWith(pkg + ".")

  /** A name of the JDK, of Scala's library or of the language: never one of the code read. */
  def foreign(name: String): Boolean =
    within("java", name) || within("javax", name) || within("scala", name) || name == "<special-ops>"

  /** Every tree inside a tree, itself first (`Program.nodes`), as far as the staging keeps the tree. */
  def nodes(t: Tree): List[Tree] = t :: (t match
    case Select(q, _)                  => nodes(q)
    case TypeApply(q, _)               => nodes(q)
    case Typed(q, _)                   => nodes(q)
    case Closure(q)                    => nodes(q)
    case Return(q, _)                  => nodes(q)
    case Bind(_, q)                    => nodes(q)
    case TypeTest(q, _)                => nodes(q)
    case Apply(f, args)                => nodes(f) ++ args.flatMap(nodes)
    case Assign(l, r)                  => nodes(l) ++ nodes(r)
    case While(l, r)                   => nodes(l) ++ nodes(r)
    case Block(stats, result)          => stats.flatMap(nodes) ++ nodes(result)
    case If(c, a, b)                   => nodes(c) ++ nodes(a) ++ nodes(b)
    case Match(on, cases)              => nodes(on) ++ cases.flatMap(nodes)
    case Alternatives(cases)           => cases.flatMap(nodes)
    case Try(body, cases, last)        => nodes(body) ++ cases.flatMap(nodes) ++ last.toList.flatMap(nodes)
    case Repeated(elems)               => elems.flatMap(nodes)
    case Inlined(bindings, body)       => bindings.flatMap(nodes) ++ nodes(body)
    case ValDef(_, _, _, rhs)          => rhs.toList.flatMap(nodes)
    case DefDef(_, _, pss, rhs, _)     => pss.flatten.flatMap(nodes) ++ rhs.toList.flatMap(nodes)
    case ClassDef(_, _, ctor, ps, body) => nodes(ctor) ++ ps.flatMap(nodes) ++ body.flatMap(nodes)
    case PackageClause(stats)          => stats.flatMap(nodes)
    case CaseDef(p, guard, body)       => nodes(p) ++ guard.toList.flatMap(nodes) ++ nodes(body)
    case Unapply(f, ps)                => nodes(f) ++ ps.flatMap(nodes)
    case _                             => Nil)

  /** The class a type is of, where it is of one (`Table.ty_class`). */
  def tyClass(t: Datum): Option[String] = t match
    case Of("TyRef", List(Text(name))) => Some(name)
    case Of("TyApp", List(c, _))       => tyClass(c)
    case Of("TyAnnot", List(u, _))     => tyClass(u)
    case Of("TyLambda", List(_, body)) => tyClass(body)
    case Of("TyAlias", List(_, named)) => tyClass(named)
    case _                             => None

  /** The type an object made is of (`Table.made`). */
  def made(t: Tree): Option[Datum] = t match
    case Apply(f, _)     => made(f)
    case TypeApply(f, _) => made(f)
    case Select(f, _)    => made(f)
    case New(ty)         => Some(ty)
    case TypeTree(ty)    => Some(ty)
    case _               => None

  /** The arguments of a constructor called: of every list (`Meaning.spine_args`). */
  def spineArgs(t: Tree): List[Tree] = t match
    case Apply(f, args)  => spineArgs(f) ++ args
    case TypeApply(f, _) => spineArgs(f)
    case _               => Nil

  /** The parameters of a method that are values (`Table.params`). */
  def params(d: DefDef): List[ValDef] = d.paramss.flatten.collect { case v: ValDef => v }

  /** Whether a parameter is taken unevaluated (`Table.by_name`). */
  def byName(p: ValDef): Boolean = p.ty match
    case Of("TyByName", _) => true
    case _                 => p.flags.contains("Inline")

  /** The definitions a method's data says it overrides. */
  def overridden(data: Datum): List[Sym] = data match
    case Of("DefDef", List(_, _, _, _, _, Many(os))) => os.map(Tree.sym)
    case _                                           => Nil

  /** A method's data with, in the place of its body, the name of the unit that runs it: what a function value
    * made by staged code holds in place of its tree.
    */
  def stub(data: Datum, unit: Sym.Local): Datum = data match
    case Of("DefDef", List(s, flags, pss, result, _, os)) =>
      val named = Datum.of("Ident", Datum.of("Local", Datum.Text(unit.name), Datum.Nat(unit.id)))
      Of("DefDef", List(s, flags, pss, result, Datum.Maybe(Some(named)), os))
    case other                                            => other
