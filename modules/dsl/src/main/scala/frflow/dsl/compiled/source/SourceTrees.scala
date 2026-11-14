package frflow.dsl.compiled.source

import frflow.core.threads.Datum
import frflow.core.threads.Datum.{Many, Maybe, Nat, Text, Truth}

/** An expression, a pattern, a clause of a file, as the tree read holds it (`FrFlow/Scala/Tree.v`, `tree`): the
  * constructor of its form, over its parts read the same way. A form the compiler's reader does not open (a
  * macro's quoted code) is `Other`, with its kind and its text.
  */
private[source] trait SourceTrees extends SourceTypes:
  import q.reflect.*

  def definition(d: Definition): Datum

  def trees(ts: List[Tree]): Datum = Many(ts.map(tree))

  /** A file's package clause is asked first: the compiler's reader takes it for a term, its name being one. */
  def tree(t: Tree): Datum = t match
    case PackageClause(pid, stats) => Datum.of("PackageClause", Text(pid.symbol.fullName), trees(stats))
    case d: Definition      => definition(d)
    case e: Term            => term(e)
    case t: TypeTree        => Datum.of("TypeTree", ty(t.tpe))
    case t: TypeBoundsTree  => Datum.of("TypeTree", ty(t.tpe))
    case other              => clause(other)

  private def term(t: Term): Datum = t match
    case Wildcard()               => Datum.of("Wildcard")
    case Ident(_)                 => Datum.of("Ident", sym(t.symbol))
    case Select(on, _)            => Datum.of("Select", tree(on), sym(t.symbol))
    case SelectOuter(on, name, n) => Datum.of("SelectOuter", tree(on), Text(name), Nat(n))
    case This(_)                  => Datum.of("This", Text(scopeKey(t.symbol)))
    case Super(on, mix)           => Datum.of("Super", tree(on), Maybe(mix.map(Text(_))))
    case Literal(c)               => Datum.of("Literal", const(c))
    case New(of)                  => Datum.of("New", ty(of.tpe))
    case Apply(f, args)           => Datum.of("Apply", tree(f), trees(args))
    case TypeApply(f, args)       => Datum.of("TypeApply", tree(f), Many(args.map(a => ty(a.tpe))))
    case NamedArg(name, arg)      => Datum.of("NamedArg", Text(name), tree(arg))
    case Typed(e, as)             => Datum.of("Typed", tree(e), ty(as.tpe))
    case Assign(to, value)        => Datum.of("Assign", tree(to), tree(value))
    case Block(stats, result)     => Datum.of("Block", trees(stats), tree(result))
    case other                    => control(other)

  private def control(t: Term): Datum = t match
    case Closure(method, as)      => Datum.of("Closure", tree(method), Maybe(as.map(ty)))
    case If(c, a, b)              => Datum.of("If", tree(c), tree(a), tree(b))
    case Match(on, cases)         => Datum.of("Match", Truth(kind(t) == "InlineMatch"), tree(on), trees(cases))
    case SummonFrom(cases)        => Datum.of("SummonFrom", trees(cases))
    case Try(body, cases, last)   => Datum.of("Try", tree(body), trees(cases), Maybe(last.map(tree)))
    case Return(e, from)          => Datum.of("Return", tree(e), sym(from))
    case While(c, body)           => Datum.of("While", tree(c), tree(body))
    case Repeated(elems, of)      => Datum.of("Repeated", trees(elems), ty(of.tpe))
    case Inlined(call, bs, body)  => Datum.of("Inlined", Maybe(call.map(tree)), trees(bs), tree(body))
    case other                    => unopened(other)

  private def clause(t: Tree): Datum = t match
    case Import(from, selectors)   => Datum.of("Imported", tree(from), Datum.texts(selectors.map(selector)))
    case Export(from, selectors)   => Datum.of("Exported", tree(from), Datum.texts(selectors.map(selector)))
    case CaseDef(p, guard, body)   => Datum.of("CaseDef", tree(p), Maybe(guard.map(tree)), tree(body))
    case Bind(_, p)                => Datum.of("Bind", sym(t.symbol), tree(p))
    case Unapply(f, given_, ps)    => Datum.of("Unapply", tree(f), trees(given_), trees(ps))
    case Alternatives(ps)          => Datum.of("Alternatives", trees(ps))
    case TypedOrTest(p, as)        => Datum.of("TypeTest", tree(p), ty(as.tpe))
    case other                     => unopened(other)

  private def kind(t: Tree): String = t.getClass.getSimpleName

  /** A tree of a form the reader gives no parts of: its kind, and its text. */
  private def unopened(t: Tree): Datum =
    Datum.of("Other", Text(kind(t)), Text(scala.util.Try(t.show).getOrElse(t.toString)))

  private def selector(s: Selector): String = s match
    case SimpleSelector(name)   => name
    case RenameSelector(a, b)   => s"$a => $b"
    case OmitSelector(name)     => s"$name => _"
    case GivenSelector(bound)   => bound.fold("given")(b => s"given ${b.tpe.show}")
