package frflow.eval.run

import frflow.core.code.{Attachment, Code, CodeTable, Impl, ScalaCode}
import frflow.core.example.CallExample
import frflow.core.expr.{Binder, Expr, Lambda, PrimOp}
import frflow.core.name.*
import frflow.core.{Sited, Theory}
import frflow.core.spec.{Node, Promise, Prose, Reliance, Statement, Written}
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType, Vocabulary}

/** A theory of one contract, for the plain-code path's tests: `echo` returns its input, `(x, r) => r === x`. */
object Echo:
  val op: SymbolName = SymbolName("echo")
  val contract: NodeId = NodeId("EchoReturnsInput")
  private val here = RelPath.fromIdentifiers("src", "Echo.scala")
  private val (x, r) = (Binder(VarId(0), "x", Ty.Str), Binder(VarId(1), "r", Ty.Str))
  private val post = Lambda(List(x, r), Expr.Prim(PrimOp.Eq, List(Expr.Var(r), Expr.Var(x)), Ty.Bool), Ty.Bool)
  private val promise = Promise[CallExample](Written(post, SourceText("(x, r) => r === x")), None, Nil)
  private val echo = Symbol(op, "the input, returned", SymbolType.Typed(Ty.FnOf(List(Ty.Str), Ty.Str)))

  /** The theory, with `code` (a Scala `String => String`) attached to the contract as plain code. */
  def theory(code: AnyRef): Theory =
    val attached = Attachment(Code.Tested(ScalaCode(Impl(1, () => code), SourceText("…"), Nil), Nil), None, here)
    val node = Node(contract, Prose("Echo returns its input.", "…"), Statement.Contract(op, promise, Reliance.Relied))
    Theory(KbName("Echo"), Vocabulary(Nil, Nil, List(echo), Nil, Nil, Nil), List(Sited(node, Span(here, 0))), Nil,
      CodeTable(Map(contract -> attached), Map.empty))
