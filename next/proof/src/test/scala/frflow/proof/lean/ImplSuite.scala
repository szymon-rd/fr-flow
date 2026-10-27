package frflow.proof.lean

import frflow.core.analysis.{Resolve, Validate}
import frflow.core.code.{Attachment, Code, CodeTable}
import frflow.core.{Elaborated, Sited, Theory}
import frflow.core.expr.Expr
import frflow.core.graph.Edge
import frflow.core.name.*
import frflow.core.spec.{Node, Reliance, Statement, Written}
import frflow.core.term.Sym
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.{Define, DefineForm, Symbol, SymbolType, ValueKind, Vocabulary}
import frflow.proof.obligation.{Hyp, Prop, Required, Substitute}

/** `impl` of a node checked against proven code and with no parts (R11.3): crm's `ExpiryJob`, a part of the claim
  * above it, about `runExpiry`, whose code is the program `expireOnce`. Its hypotheses are what the code relies on,
  * `SharesExpire` on `expire`, which `expireOnce` calls; the obligation is the one today's `ExpiryJob/Spec.lean`
  * states.
  */
class ImplSuite extends munit.FunSuite:
  private val (store, big) = (Ty.Data(TypeName("CrmStore")), Ty.Num(NumKind.Big))
  private val (root, job, shares) = (NodeId("RecordsKept"), ExpiryIr.expiryJob, ExpiryIr.sharesExpire)
  private val here = Span(RelPath.parse("Crm.scala").toOption.get, 0)
  private def sited(id: NodeId, s: Statement) = Sited(Node(id, s"${id.value} holds.", s), here)
  private val holds = [T[_]] => (s: Sym[T]) => s.bool(true)
  private val (runExpiry, expire) = (SymbolName("runExpiry"), SymbolName("expire"))
  private val (runType, expireType) = (Ty.FnOf(List(big), Ty.FlowOf(store, None)), Ty.FnOf(List(store, big), store))
  /** A formula mentioning `op` (all `impl` reads of it: the Definition it constrains). */
  private def about(op: SymbolName, ty: Ty) =
    Written.formula([T[_]] => (s: Sym[T]) => s.eq[Any](s.param[Any](op, ty), s.param[Any](op, ty)), SourceText("…"))
  private def claimed(f: Written[Expr]) = Statement.Claim(f, Reliance.Relied)

  private val theory = Theory(KbName("Crm"),
    Vocabulary(Nil, Nil, List(
      Symbol(expire, "what expiring leaves", SymbolType.Typed(expireType), ValueKind.Definition),
      Symbol(runExpiry, "a run of the expiry job", SymbolType.Typed(runType), ValueKind.Definition)),
      List(Define(DefName("expireOnce"), ExpiryIr.expireOnce, DefineForm.Flow),
      Define(DefName("expireOnce_run"), ExpiryIr.expireOnce, DefineForm.RunOf(DefName("expireOnce")))), Nil, Nil),
    List(sited(root, claimed(Written.formula(holds, SourceText("…")))),
      sited(job, claimed(about(runExpiry, runType))), sited(shares, claimed(about(expire, expireType)))),
    List(Edge.PartOf(job, root), Edge.PartOf(shares, root)),
    CodeTable(Map(runExpiry -> Attachment(Code.ProvenFlow(DefName("expireOnce")), here.file),
      expire -> Attachment(Code.Provided, here.file)), Map.empty)) // `expire`'s meaning is not this test's

  test("a node with proven code and no parts: impl over what its code relies on, as today's ExpiryJob/Spec.lean") {
    val valid = Validate(Elaborated(theory, Map.empty, Nil)).fold(ps => fail(ps.toString), identity)
    val r = Resolve(valid)
    assertEquals((r.theory.refinement.parts(job), r.reliesOn(job)), (Nil, List(shares)))
    val byCode = Map(SymbolName("runExpiry") -> Substitute.Code(ExpiryIr.expireOnceRun))
    assertEquals(Required.impl(r, job).map(o => (o.goal, o.doc)), List((Prop.over(Nil, Prop.Implies(
      List(Hyp.of(shares)), Prop.ClaimOf(job, byCode))),
      "Every result of expireOnce_run meets ExpiryJob, given what SharesExpire promise.")))
  }
