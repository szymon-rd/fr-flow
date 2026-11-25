package frflow.core.staged

import frflow.core.code.Datum
import frflow.core.code.Datum.{Of, Text}

/** A `match` and a `try` staged (`Meaning.denote_step`, `pmatch_step`): which case takes a value is decided
  * when the code runs; what each case binds is known here.
  */
private[staged] trait StagePatterns extends StageCalls:
  import Tree.*

  /** The cases in order: the first whose pattern takes the value and whose guard holds. */
  def matched(v: V, cases: List[Tree])(using Env): P =
    tryEach(v, cases, op("no_case"))

  private def tryEach(v: V, cases: List[Tree], none: P)(using e: Env): P = cases match
    case Nil                            => none
    case CaseDef(p, guard, body) :: rest =>
      val next = e.names.fresh("next")
      val here = (inner: Env) => guarded(guard, body, P.Use(next))(using inner)
      P.Share(next, tryEach(v, rest, none), taken(p, v, P.Use(next))(here))
    case _                              => P.Stuck("a case that is no case")

  private def guarded(guard: Option[Tree], body: Tree, otherwise: P)(using Env): P = guard match
    case None    => expr(body)
    case Some(g) => bind(expr(g), "guard")(b => P.Truth(b, expr(body), otherwise))

  /** A pattern on a value (`Meaning.pmatch_step`): `hit` in the scope it leaves where it takes the value,
    * `miss` where it does not.
    */
  private def taken(p: Tree, v: V, miss: P)(hit: Env => P)(using e: Env): P = p match
    case Wildcard                        => hit(e)
    case Bind(s, inner)                  => taken(inner, v, miss)(after => hit(after.having(s.key, Bound.Plain(v))))
    case Literal(Of("CFloat" | "CDouble", _)) => P.Stuck("a floating-point constant in a pattern")
    case Literal(c)                      => tested(op("eq_", value(v), value(constantOf(c))), miss)(hit(e))
    case TypeTest(inner, ty)             => tested(op("isa", value(v), Arg.Type(ty)), miss)(taken(inner, v, miss)(hit))
    case Typed(inner, ty)                => tested(op("isa", value(v), Arg.Type(ty)), miss)(taken(inner, v, miss)(hit))
    case Alternatives(ps)                =>
      val found = e.names.fresh("found")
      P.Share(found, hit(e), ps.foldRight(miss)((q, otherwise) => taken(q, v, otherwise)(_ => P.Use(found))))
    case u: Unapply                      => unapplied(u, v, miss)(hit)
    case Ident(s)                        =>
      bind(ident(s, Nil, Nil), "same")(x => tested(op("eq_", value(v), value(x)), miss)(hit(e)))
    case Select(on, s)                   =>
      bind(select(expr(on), s, Nil, Nil), "same")(x => tested(op("eq_", value(v), value(x)), miss)(hit(e)))
    case _                               => P.Stuck("a pattern of a form with no meaning here")

  private def constantOf(c: Datum): V = c match
    case Of("CUnit", _) => V.Unit
    case _              => V.Const(c)

  private def tested(test: P, miss: P)(hit: => P)(using Env): P = bind(test, "is")(b => P.Truth(b, hit, miss))

  /** An extractor's pattern: the extractor is called on the value, and what it gives is taken apart. */
  private def unapplied(u: Unapply, v: V, miss: P)(hit: Env => P)(using e: Env): P =
    val ps = u.ps
    bind(applied(u.f, Nil, List(Left(v))), "extracted") { r =>
      val names = ps.map(_ => e.names.fresh("part"))
      val each = ps.zip(names).foldRight(hit)((part, rest) => after =>
        taken(part._1, V.Var(part._2), miss)(rest)(using after))
      P.Parts(op("unapplied", Arg.Count(ps.size), value(r)), names, each(e), miss)
    }

  /** A handler's pattern that takes whatever is thrown (`Meaning.takes_all`): `_: Throwable`, named or not. */
  private def takesAll(p: Tree): Boolean = p match
    case Typed(Wildcard, ty)    => allThrown(ty)
    case TypeTest(Wildcard, ty) => allThrown(ty)
    case Bind(_, q)             => takesAll(q)
    case _                      => false

  private def allThrown(ty: Datum): Boolean = ty match
    case Of("TyRef", List(Text(name))) => name == "java.lang.Throwable"
    case Of("TyAlias", List(_, named)) => allThrown(named)
    case Of("TyAnnot", List(u, _))     => allThrown(u)
    case _                             => false

  private def namedAll(p: Tree, v: V, e: Env): Env = p match
    case Bind(s, q) => namedAll(q, v, e).having(s.key, Bound.Plain(v))
    case _          => e

  def tried(t: Try)(using e: Env): P =
    val handler = Option.when(t.cases.nonEmpty) {
      val (thrown, held) = (e.names.fresh("thrown"), e.names.fresh("caught"))
      Handler(thrown, held, handled(V.Var(held), t.cases, op("rethrow", variable(thrown))))
    }
    P.Handle(expr(t.body), handler, t.last.map(expr))

  private def handled(v: V, cases: List[Tree], none: P)(using e: Env): P = cases match
    case Nil                                => none
    case CaseDef(p, guard, body) :: rest    =>
      val next = e.names.fresh("next")
      val here = (inner: Env) => guarded(guard, body, P.Use(next))(using inner)
      P.Share(next, handled(v, rest, none),
        if takesAll(p) then here(namedAll(p, v, e)) else taken(p, v, P.Use(next))(here))
    case _                                  => P.Stuck("a handler that is no case")
