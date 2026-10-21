package frflow.ir

/** Intermediate representation of the Scala subset FrFlow translates.
  *
  * The macro lifter (`frflow.lift`) produces it from typed Scala trees at compile
  * time; the Lean backend (`frflow.render`) prints it. Names are Lean names:
  * the Scala owner chain without the package, for example `UserId.Anonymous`.
  */

/** Types. Scala `Boolean` is a proposition on the Lean side. */
enum Type:
  case Bool, Int, Str, Unit
  /** A user ADT: a case class (structure) or an enum (inductive). */
  case Named(name: String)
  case ListOf(elem: Type)
  case SetOf(elem: Type)
  case MapOf(key: Type, value: Type)
  case OptionOf(elem: Type)
  case TupleOf(elems: List[Type])
  case Fun(params: List[Type], result: Type)

  /** Names of the ADTs this type refers to. */
  def references: Set[String] = this match
    case Named(n)          => Set(n)
    case ListOf(e)         => e.references
    case SetOf(e)          => e.references
    case MapOf(k, v)       => k.references ++ v.references
    case OptionOf(e)       => e.references
    case TupleOf(es)       => es.flatMap(_.references).toSet
    case Fun(ps, r)        => ps.flatMap(_.references).toSet ++ r.references
    case Bool | Int | Str | Unit => Set.empty

  /** Whether values of this type can be computed and compared at run time. */
  def isData: Boolean = this match
    case Fun(_, _)   => false
    case ListOf(e)   => e.isData
    case SetOf(e)    => e.isData
    case MapOf(k, v) => k.isData && v.isData
    case OptionOf(e) => e.isData
    case TupleOf(es) => es.forall(_.isData)
    case _           => true

/** Built-in operations. Each has a fixed Lean rendering (see `frflow.render.LeanPrinter`). */
enum Prim:
  // logic
  case And, Or, Not, Implies, Eq, Ne
  // integers
  case Add, Sub, Mul, Div, Mod, Neg, Lt, Le, Gt, Ge, Max, Min
  // strings
  case Concat
  // lists
  case ListNil, ListCons, ListOf, ListAppend, ListContains, ListForall, ListExists, ListMap, ListFilter,
    ListLength, ListIsEmpty, ListNonEmpty, ListHeadOption
  // options
  case OptSome, OptNone, OptGetOrElse, OptIsDefined, OptIsEmpty, OptContains, OptExists, OptForall, OptMap,
    OptFlatMap, OptOrElse
  // sets
  case SetEmpty, SetOf, SetContains, SetIncl, SetExcl, SetUnion, SetIntersect, SetDiff, SetForall, SetExists,
    SetIsEmpty, SetSubsetOf
  // maps
  case MapEmpty, MapGet, MapGetOrElse, MapUpdated, MapRemoved, MapContains, MapIsEmpty, MapForall, MapExists,
    MapKeySet
  // tuples
  case TupleOf, Fst, Snd

/** Quantifiers. They appear only in specifications and cannot be executed. */
enum Quantifier:
  case All, Ex

enum Pattern:
  case Wild
  /** `x @ p`; a plain variable pattern is `Bind(x, Wild)`. */
  case Bind(name: String, pat: Pattern)
  /** Constructor pattern: an ADT constructor, `Some`/`None`, `::`/`Nil` or a tuple. */
  case Ctor(ctor: String, args: List[Pattern])
  case Lit(value: Expr)

  def binders: List[String] = this match
    case Wild          => Nil
    case Bind(n, p)    => n :: p.binders
    case Ctor(_, args) => args.flatMap(_.binders)
    case Lit(_)        => Nil

final case class Case(pat: Pattern, body: Expr)

final case class Param(name: String, tpe: Type)

enum Expr:
  case Var(name: String)
  case BoolLit(value: Boolean)
  case IntLit(value: BigInt)
  case StrLit(value: String)
  case UnitLit
  /** A field of a case class value. */
  case Field(target: Expr, field: String)
  /** Constructor application. `ctor` is the Lean constructor name (`UserId.mk`, `Action.Read`). */
  case Construct(ctor: String, args: List[Expr])
  /** `target.copy(f = e, ...)`. */
  case With(target: Expr, updates: List[(String, Expr)])
  /** Call of a translated user definition. For a method, the receiver is the first argument. */
  case Call(fn: String, args: List[Expr], method: Boolean)
  /** Reference to a translated user value without parameters (an object `val` or nullary `def`). */
  case Ref(name: String)
  case PrimOp(op: Prim, args: List[Expr], tpe: Option[Type])
  case Lam(params: List[Param], body: Expr)
  case App(fn: Expr, args: List[Expr])
  case If(cond: Expr, thenp: Expr, elsep: Expr)
  case Match(scrutinee: Expr, cases: List[Case])
  case Let(name: String, tpe: Type, value: Expr, body: Expr)
  case Quant(q: Quantifier, params: List[Param], body: Expr)

  def children: List[Expr] = this match
    case Field(t, _)        => List(t)
    case Construct(_, as)   => as
    case With(t, us)        => t :: us.map(_._2)
    case Call(_, as, _)     => as
    case PrimOp(_, as, _)   => as
    case Lam(_, b)          => List(b)
    case App(f, as)         => f :: as
    case If(c, t, e)        => List(c, t, e)
    case Match(s, cs)       => s :: cs.flatMap(c => patExprs(c.pat) :+ c.body)
    case Let(_, _, v, b)    => List(v, b)
    case Quant(_, _, b)     => List(b)
    case _                  => Nil

  private def patExprs(p: Pattern): List[Expr] = p match
    case Pattern.Lit(e)        => List(e)
    case Pattern.Bind(_, q)    => patExprs(q)
    case Pattern.Ctor(_, args) => args.flatMap(patExprs)
    case Pattern.Wild          => Nil

  /** All subexpressions, this one first. */
  def subterms: Iterator[Expr] = Iterator.single(this) ++ children.iterator.flatMap(_.subterms)

  /** Names of translated user definitions this expression uses. */
  def calls: Set[String] = subterms.collect {
    case Call(fn, _, _) => fn
    case Ref(n)         => n
  }.toSet

  def hasQuantifier: Boolean = subterms.exists(_.isInstanceOf[Quant])

  def freeVars: Set[String] = this match
    case Var(n)             => Set(n)
    case Lam(ps, b)         => b.freeVars -- ps.map(_.name)
    case Quant(_, ps, b)    => b.freeVars -- ps.map(_.name)
    case Let(n, _, v, b)    => v.freeVars ++ (b.freeVars - n)
    case Match(s, cs)       => s.freeVars ++ cs.flatMap(c => c.body.freeVars -- c.pat.binders)
    case e                  => e.children.flatMap(_.freeVars).toSet

object Expr:
  def and(xs: List[Expr]): Expr = xs match
    case Nil      => BoolLit(true)
    case x :: Nil => x
    case _        => xs.reduceRight((a, b) => PrimOp(Prim.And, List(a, b), None))

/** A lambda lifted from Scala, with its source text. */
final case class Lifted(params: List[Param], result: Type, body: Expr, source: String, position: String):
  def lam: Expr.Lam = Expr.Lam(params, body)

  /** The body with parameters renamed to `names` (capture-avoiding). */
  def bodyWith(names: List[String]): Expr =
    require(names.size == params.size, s"expected ${params.size} names")
    Rename(params.map(_.name).zip(names).toMap, body)

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

final case class FieldDef(name: String, tpe: Type, doc: String)

final case class CtorDef(name: String, fields: List[FieldDef], doc: String)

enum AdtShape:
  /** A case class: one constructor `mk`. */
  case Product(fields: List[FieldDef])
  /** A Scala 3 enum: several constructors. */
  case Sum(ctors: List[CtorDef])

/** A user ADT. `scalaName` is the fully qualified Scala name. */
final case class AdtDef(name: String, scalaName: String, shape: AdtShape, doc: String, source: String):
  def references: Set[String] = shape match
    case AdtShape.Product(fs) => fs.flatMap(_.tpe.references).toSet - name
    case AdtShape.Sum(cs)     => cs.flatMap(_.fields.flatMap(_.tpe.references)).toSet - name

  def fieldNames: List[String] = shape match
    case AdtShape.Product(fs) => fs.map(_.name)
    case AdtShape.Sum(_)      => Nil

/** A user function: a method of an ADT (`self` first), a function in an object,
  * or a value in an object (no parameters).
  */
final case class FunDef(
    name: String,
    scalaName: String,
    params: List[Param],
    result: Type,
    body: Expr,
    doc: String,
    source: String
):
  def references: Set[String] = (params.flatMap(_.tpe.references) ++ result.references).toSet ++
    body.subterms.flatMap {
      case Expr.Lam(ps, _)       => ps.flatMap(_.tpe.references)
      case Expr.Quant(_, ps, _)  => ps.flatMap(_.tpe.references)
      case Expr.Let(_, t, _, _)  => t.references
      case Expr.PrimOp(_, _, t)  => t.toList.flatMap(_.references)
      case _                     => Nil
    }.toSet

/** Definitions an expression depends on, keyed by Lean name. */
final case class Defs(adts: Map[String, AdtDef], funs: Map[String, FunDef]):
  def ++(o: Defs): Defs = Defs(adts ++ o.adts, funs ++ o.funs)

object Defs:
  val empty: Defs = Defs(Map.empty, Map.empty)

/** Result of the lifter for one Scala lambda or type. */
final case class LiftResult(lifted: Option[Lifted], tpe: Type, defs: Defs)

// ---------------------------------------------------------------------------
// Capture-avoiding renaming of variables
// ---------------------------------------------------------------------------

object Rename:
  def apply(map: Map[String, String], e: Expr): Expr = go(map, e)

  private def fresh(base: String, avoid: Set[String]): String =
    Iterator.from(1).map(i => s"${base}_$i").find(n => !avoid(n)).get

  private def go(m: Map[String, String], e: Expr): Expr =
    import Expr.*
    if m.isEmpty then e
    else
      val targets = m.values.toSet
      def binders(ps: List[Param], body: Expr): (List[Param], Map[String, String]) =
        // binders shadow the renaming; binders that collide with a target are renamed themselves
        var inner = m -- ps.map(_.name)
        val avoid = targets ++ body.freeVars
        val ps2 = ps.map { p =>
          if targets(p.name) then
            val n = fresh(p.name, avoid ++ ps.map(_.name))
            inner = inner + (p.name -> n)
            p.copy(name = n)
          else p
        }
        (ps2, inner)
      e match
        case Var(n)               => Var(m.getOrElse(n, n))
        case Lam(ps, b) =>
          val (ps2, inner) = binders(ps, b)
          Lam(ps2, go(inner, b))
        case Quant(q, ps, b) =>
          val (ps2, inner) = binders(ps, b)
          Quant(q, ps2, go(inner, b))
        case Let(n, t, v, b) =>
          val (ps2, inner) = binders(List(Param(n, t)), b)
          Let(ps2.head.name, t, go(m, v), go(inner, b))
        case Match(s, cs) =>
          Match(go(m, s), cs.map { c =>
            val bs = c.pat.binders
            var inner = m -- bs
            val ren = bs.filter(targets).map(b => b -> fresh(b, targets ++ c.body.freeVars ++ bs)).toMap
            inner = inner ++ ren
            Case(renamePat(ren, c.pat), go(inner, c.body))
          })
        case Field(t, f)          => Field(go(m, t), f)
        case Construct(c, as)     => Construct(c, as.map(go(m, _)))
        case With(t, us)          => With(go(m, t), us.map((f, x) => f -> go(m, x)))
        case Call(f, as, meth)    => Call(f, as.map(go(m, _)), meth)
        case PrimOp(op, as, t)    => PrimOp(op, as.map(go(m, _)), t)
        case App(f, as)           => App(go(m, f), as.map(go(m, _)))
        case If(c, t, el)         => If(go(m, c), go(m, t), go(m, el))
        case other                => other

  private def renamePat(ren: Map[String, String], p: Pattern): Pattern = p match
    case Pattern.Bind(n, q)    => Pattern.Bind(ren.getOrElse(n, n), renamePat(ren, q))
    case Pattern.Ctor(c, args) => Pattern.Ctor(c, args.map(renamePat(ren, _)))
    case other                 => other
