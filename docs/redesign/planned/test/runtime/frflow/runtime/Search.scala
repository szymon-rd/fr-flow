package frflow.runtime

import frflow.core.code.{Attachment, Code, CodeTable, Impl, ScalaCode}
import frflow.core.example.CallExample
import frflow.core.expr.{Binder, Expr, Lambda, PrimOp}
import frflow.core.name.*
import frflow.core.{Sited, Theory}
import frflow.core.spec.{Node, Promise, Prose, Reliance, Statement, Written}
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType, Vocabulary}
import frflow.dsl.term.Values

/** crm's read side in small: the contract's code for `search` calls `fetch`, an outside system's operation whose
  * adapter is attached to the assumption about it. Both promise to return the query.
  */
object Search:
  val (search, fetch) = (SymbolName("search"), SymbolName("fetch"))
  val (contract, assumption) = (NodeId("SearchReturnsQuery"), NodeId("RecordsByQuery"))
  private val here = RelPath.fromIdentifiers("src", "Search.scala")
  private val (q, r) = (Binder(VarId(0), "q", Ty.Str), Binder(VarId(1), "r", Ty.Str))
  private val post = Lambda(List(q, r), Expr.Prim(PrimOp.Eq, List(Expr.Var(r), Expr.Var(q)), Ty.Bool), Ty.Bool)
  private val promise = Promise[CallExample](Written(post, SourceText("(q, r) => r === q")), None, Nil)
  private def op(s: SymbolName) = Symbol(s, "the query's records", SymbolType.Typed(Ty.FnOf(List(Ty.Str), Ty.Str)))

  /** The contract's code: `fetch` as bound where it runs, called on the query. */
  private val searching = Impl(1, () => Values.read(fetch) match
    case Some(f: Function1[String, String] @unchecked) => (x: String) => f(x)
    case _                                             => throw IllegalStateException("fetch is not bound"))

  /** The theory, with `adapter` (a Scala `String => String`) attached to the assumption when given. */
  def theory(adapter: Option[AnyRef]): Theory =
    val nodes = List(
      Node(contract, Prose("Search returns the query.", "…"), Statement.Contract(search, promise, Reliance.Relied)),
      Node(assumption, Prose("The store returns the query.", "…"), Statement.AssumedCall(fetch, promise)))
    val code = Map(contract -> attached(searching, List(fetch))) ++
      adapter.map(a => assumption -> attached(Impl(1, () => a), Nil))
    Theory(KbName("Search"), Vocabulary(Nil, Nil, List(op(search), op(fetch)), Nil, Nil, Nil),
      nodes.map(Sited(_, Span(here, 0))), Nil, CodeTable(code, Map.empty))

  private def attached(impl: Impl, calls: List[SymbolName]): Attachment =
    Attachment(Code.Tested(ScalaCode(impl, SourceText("…"), Nil), calls), None, here)
