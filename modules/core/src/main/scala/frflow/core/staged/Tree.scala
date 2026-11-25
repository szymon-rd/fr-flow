package frflow.core.staged

import frflow.core.code.Datum

/** How the tree read names a definition (`FrFlow/Scala/Tree.v`, `sym`). */
enum Sym:
  case NoSym
  case Member(owner: String, name: String, signature: String)
  case Local(name: String, id: Int)

  /** The text a variable in scope is named by (`Value.key`). */
  def key: String = this match
    case Local(name, id)       => s"$name#$id"
    case Member(owner, name, _) => s"$owner.$name"
    case NoSym                 => ""

/** The tree read (`FrFlow/Scala/Tree.v`, `tree`), as the staging takes it apart. A type and a constant stay the
  * data they are read as: the staging passes them on. A form the meaning gives no meaning is `Unmeant`.
  */
enum Tree:
  case Ident(s: Sym)
  case Select(on: Tree, s: Sym)
  case This(cls: String)
  case Literal(c: Datum)
  case New(ty: Datum)
  case Apply(f: Tree, args: List[Tree])
  case TypeApply(f: Tree, targs: List[Datum])
  case Typed(e: Tree, ty: Datum)
  case Assign(to: Tree, value: Tree)
  case Block(stats: List[Tree], result: Tree)
  case Closure(of: Tree)
  case If(c: Tree, yes: Tree, no: Tree)
  case Match(on: Tree, cases: List[Tree])
  case Try(body: Tree, cases: List[Tree], last: Option[Tree])
  case Return(e: Tree, from: Sym)
  case While(c: Tree, body: Tree)
  case Repeated(elems: List[Tree])
  case Inlined(bindings: List[Tree], body: Tree)
  case ValDef(s: Sym, flags: List[String], ty: Datum, rhs: Option[Tree])
  case DefDef(s: Sym, flags: List[String], paramss: List[List[Tree]], rhs: Option[Tree], data: Datum)
  case ClassDef(name: String, flags: List[String], ctor: Tree, parents: List[Tree], body: List[Tree])
  case PackageClause(stats: List[Tree])
  case CaseDef(p: Tree, guard: Option[Tree], body: Tree)
  case Bind(s: Sym, p: Tree)
  case Unapply(f: Tree, ps: List[Tree])
  case Alternatives(ps: List[Tree])
  case TypeTest(p: Tree, ty: Datum)
  case TypeTree(ty: Datum)
  case Wildcard
  case Unmeant(what: String)

object Tree:
  import Datum.{Many, Maybe, Nat, Of, Text}

  def sym(d: Datum): Sym = d match
    case Of("Member", List(Text(o), Text(n), Text(s))) => Sym.Member(o, n, s)
    case Of("Local", List(Text(n), Nat(i)))            => Sym.Local(n, i)
    case _                                             => Sym.NoSym

  private def all(d: Datum): List[Tree] = d match
    case Many(elems) => elems.map(of)
    case _           => Nil

  private def maybe(d: Datum): Option[Tree] = d match
    case Maybe(value) => value.map(of)
    case _            => None

  private def texts(d: Datum): List[String] = d match
    case Many(elems) => elems.collect { case Text(t) => t }
    case _           => Nil

  private def datas(d: Datum): List[Datum] = d match
    case Many(elems) => elems
    case _           => Nil

  def of(d: Datum): Tree = d match
    case Of("Ident", List(s))                => Ident(sym(s))
    case Of("Select", List(on, s))           => Select(of(on), sym(s))
    case Of("This", List(Text(cls)))         => This(cls)
    case Of("Literal", List(c))              => Literal(c)
    case Of("New", List(t))                  => New(t)
    case Of("Apply", List(f, args))          => Apply(of(f), all(args))
    case Of("TypeApply", List(f, targs))     => TypeApply(of(f), datas(targs))
    case Of("NamedArg", List(_, arg))        => of(arg)
    case Of("Typed", List(e, t))             => Typed(of(e), t)
    case Of("Assign", List(to, value))       => Assign(of(to), of(value))
    case Of("Block", List(stats, result))    => Block(all(stats), of(result))
    case Of("Closure", List(m, _))           => Closure(of(m))
    case Of("If", List(c, a, b))             => If(of(c), of(a), of(b))
    case Of("Match", List(_, on, cases))     => Match(of(on), all(cases))
    case Of("Try", List(b, cases, last))     => Try(of(b), all(cases), maybe(last))
    case Of("Return", List(e, from))         => Return(of(e), sym(from))
    case Of("While", List(c, body))          => While(of(c), of(body))
    case Of("Repeated", List(elems, _))      => Repeated(all(elems))
    case Of("Inlined", List(_, bs, body))    => Inlined(all(bs), of(body))
    case other                               => defined(other)

  private def defined(d: Datum): Tree = d match
    case Of("ValDef", List(s, flags, t, rhs))            => ValDef(sym(s), texts(flags), t, maybe(rhs))
    case Of("DefDef", List(s, flags, pss, _, rhs, _))    =>
      DefDef(sym(s), texts(flags), datas(pss).map(all), maybe(rhs), d)
    case Of("ClassDef", List(Text(n), fs, ctor, ps, _, body)) =>
      ClassDef(n, texts(fs), of(ctor), all(ps), all(body))
    case Of("PackageClause", List(_, stats))             => PackageClause(all(stats))
    case Of("CaseDef", List(p, guard, body))             => CaseDef(of(p), maybe(guard), of(body))
    case Of("Bind", List(s, p))                          => Bind(sym(s), of(p))
    case Of("Unapply", List(f, _, ps))                   => Unapply(of(f), all(ps))
    case Of("Alternatives", List(ps))                    => Alternatives(all(ps))
    case Of("TypeTest", List(p, t))                      => TypeTest(of(p), t)
    case Of("TypeTree", List(t))                         => TypeTree(t)
    case Of("Wildcard", Nil)                             => Wildcard
    case Of(other, _)                                    => Unmeant(other)
    case _                                               => Unmeant("data that is no tree")
