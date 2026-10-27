package frflow.eval.run

import frflow.core.code.{Attachment, Code, CodeTable, Impl, ScalaCode}
import frflow.core.name.*
import frflow.core.{Sited, Theory}
import frflow.core.spec.{Node, Reliance, Statement, Written}
import frflow.core.term.{Bound, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType, ValueKind, Vocabulary}

/** A theory of one claim, for the plain-code path's tests: `echo` returns its input, written as a claim:
  * `forall((x: Term[String]) => echo(x) === x)`, its post over the input `x`.
  */
object Echo:
  val op: SymbolName = SymbolName("echo")
  val claim: NodeId = NodeId("EchoReturnsInput")
  private val here = RelPath.fromIdentifiers("src", "Echo.scala")
  private val echo =
    Symbol(op, "the input, returned", SymbolType.Typed(Ty.FnOf(List(Ty.Str), Ty.Str)), ValueKind.Definition)

  private val formula = Written.formula([T[_]] => (s: Sym[T]) => s.forall(Bound[String]("x", Ty.Str))(x =>
    s.eq[String](s.app(s.param[String => String](op, Ty.FnOf(List(Ty.Str), Ty.Str)), x), x)),
    SourceText("forall((x: Term[String]) => echo(x) === x)"))

  /** `echo("hi") === "hi"`, an example's fact. */
  val example: Written[frflow.core.expr.Expr] = Written.formula([T[_]] => (s: Sym[T]) =>
    s.eq[String](s.app(s.param[String => String](op, Ty.FnOf(List(Ty.Str), Ty.Str)), hi(s)), hi(s)),
    SourceText("echo(\"hi\") is \"hi\""))
  private def hi[T[_]](s: Sym[T]): T[String] = s.lit("hi", frflow.core.expr.Value.Str("hi"), Ty.Str)

  /** The theory, with `code` (a Scala `String => String`) as `echo`'s plain code. */
  def theory(code: AnyRef): Theory =
    val attached = Attachment(Code.Tested(ScalaCode(Impl(1, _ => code), SourceText("…"), Nil), Nil), here)
    val node = Node(claim, "Echo returns its input.", Statement.Claim(formula, Reliance.Relied))
    Theory(KbName("Echo"), Vocabulary(Nil, Nil, List(echo), Nil, Nil, Nil), List(Sited(node, Span(here, 0))), Nil,
      CodeTable(Map(op -> attached), Map.empty))
