package frflow.eval.run

import frflow.core.code.{Attachment, Code, CodeTable, Impl, ScalaCode, Values}
import frflow.core.{Elaborated, Sited, Theory}
import frflow.core.expr.Binder
import frflow.core.name.*
import frflow.core.spec.{Node, Reliance, Statement, Written}
import frflow.core.term.{Bound, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, Symbol, SymbolType, ValueKind, Vocabulary}
import frflow.eval.{Fn, ScalaValue, Semantics}

/** The values a call reads, made without asking for what FrFlow can build: a Definition given its meaning only by a
  * proven define (crm's `expire`, keycloak's `step`) is its define, run by the evaluator.
  */
class WiringSuite extends munit.FunSuite:
  private val (outer, inner) = (SymbolName("outer"), SymbolName("inner"))
  private val here = RelPath.fromIdentifiers("src", "Wiring.scala")
  private val x = Binder(VarId.level(0), "x", Ty.Str)
  private val same = Define(DefName("same"),
    Written.lambda(List(x), [T[_]] => (s: Sym[T]) => s.free[String](x), SourceText("x => x")), DefineForm.Function)
  private def op(s: SymbolName) =
    Symbol(s, "a string, returned", SymbolType.Typed(Ty.FnOf(List(Ty.Str), Ty.Str)), ValueKind.Definition)
  private def formula(op: SymbolName) = Written.formula([T[_]] => (s: Sym[T]) => s.forall(Bound[String]("x", Ty.Str))(
    x => s.eq[String](s.app(s.param[String => String](op, Ty.FnOf(List(Ty.Str), Ty.Str)), x), x)), SourceText("…"))
  private def claim(id: String, s: SymbolName) = Sited(Node(NodeId(id), s"$id returns its input.",
    Statement.Claim(formula(s), Reliance.Relied)), Span(here, 0))
  private val calling = Code.Tested(ScalaCode(Impl(1, _ => (s: String) => s), SourceText("…"), Nil), List(inner))
  private val theory = Theory(KbName("Wiring"), Vocabulary(Nil, Nil, List(op(outer), op(inner)), List(same), Nil),
    List(claim("Outer", outer), claim("Inner", inner)), Nil, CodeTable(Map(
      outer -> Attachment(calling, here), inner -> Attachment(Code.Proven(DefName("same")), here)), Map.empty))
  private val wiring = Wiring(Semantics(Elaborated(theory, Map.empty, Nil)), theory)

  test("a Definition whose meaning is only a proven define is wired as its define, and not asked for") {
    assertEquals(wiring.needed(NodeId("Outer")), Nil)
    val called = wiring.values(Values.none).get(inner).collect { case f: AnyRef => Fn.call(f, List(ScalaValue("hi"))) }
    assertEquals(called, Some(ScalaValue("hi")))
  }
