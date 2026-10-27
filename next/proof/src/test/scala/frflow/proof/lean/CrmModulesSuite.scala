package frflow.proof.lean

import frflow.core.name.{DefName, SymbolName, TypeName}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.{Define, DefineForm}
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{LowerModels, LowerObligation, LowerProp}
import frflow.proof.lean.print.*
import frflow.proof.obligation.*
import L.*

/** Four modules of `examples/crm/lean/FrFlowGen/Crm` (copied into the resources) print byte for byte from their AST;
  * the post of `ExpiryJob` and the steps of `expireOnce` are lowered from the IR (`ExpiryIr`).
  */
class CrmModulesSuite extends munit.FunSuite:
  private def file(path: String): String =
    scala.io.Source.fromResource(s"crm/$path", getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  private val (store, big) = (Ty.Data(TypeName("CrmStore")), Ty.Num(NumKind.Big))
  private val crmStore = n("CrmStore")
  private val world = n("World")
  private val expireType = arrows(crmStore, n("Int"), crmStore)

  test("Boundaries.lean: the class, the model, World, the instance and its lemmas, from the boundary and its model") {
    val imports = List("Types", "Domain.Def_replaceAbout", "Domain.Def_aboutRecord").map("FrFlowGen.Crm." + _)
    val decls = LowerModels(ExpiryIr.env, ExpiryIr.reserved).decls(List(CrmModels.boundary -> CrmModels.model), Nil)
    val m = module("FrFlowGen.Crm.Boundaries", imports, "Crm", decls*)
    assertEquals(Print.module(m), file("Boundaries.lean"))
  }

  test("Domain/Def_expireOnce.lean: a flow generic in its monad, with implicit and instance binders") {
    val body = ExpiryIr.lowered(ExpiryIr.expireOnce)
    val d = Decl.Def(defs, nm("expireOnce"), List(LBinder.Implicit(nm("m"), arrows(n("Type"), n("Type"))),
      LBinder.Instance(app(n("Monad"), n("m"))), LBinder.Instance(app(n("Database"), n("m"))), x("expire", expireType)),
      arrows(n("Int"), app(n("m"), crmStore)), body)
    val imports = List("Types", "Boundaries", "Domain.Def_changedIds").map("FrFlowGen.Crm." + _)
    val m = module("FrFlowGen.Crm.Domain.Def_expireOnce", imports, "Crm", d, Decl.MatchEqns)
    assertEquals(Print.module(m), file("Domain/Def_expireOnce.lean"))
  }

  test("Domain/Def_expireOnce_run.lean: a flow's run on the models") {
    val run = Define(DefName("expireOnce_run"), ExpiryIr.expireOnce, DefineForm.RunOf(DefName("expireOnce")))
    val d = LowerModels(ExpiryIr.env, ExpiryIr.reserved)
      .run(run, DefName("expireOnce"), List(SymbolName("expire") -> Ty.FnOf(List(store, big), store)))
    val imports = List("Types", "Boundaries", "Domain.Def_expireOnce").map("FrFlowGen.Crm." + _)
    val m = module("FrFlowGen.Crm.Domain.Def_expireOnce_run", imports, "Crm", d, Decl.MatchEqns)
    assertEquals(Print.module(m), file("Domain/Def_expireOnce_run.lean"))
  }

  private val runType = arrows(n("Int"), par(arrows(world, par(times(crmStore, world)))))
  private def run(i: String) = LExpr.Dot(par(app(n("runExpiry"), n("x0"), n("x1"))), i)
  private val post = Decl.Def(defs, nm("post"), List(x("expire", expireType)),
    arrows(n("Int"), crmStore, world, world, n("Prop")), ExpiryIr.lowered(ExpiryIr.post))
  private val claim = Decl.Def(defs, nm("claim"), List(x("expire", expireType), x("runExpiry", runType)), n("Prop"),
    LExpr.Forall(List(x("x0", n("Int")), x("x1", world)),
      app(par(app(c("Crm.ExpiryJob.post"), n("expire"))), n("x0"), run("1"), n("x1"), run("2"))))
  private val obligations = LowerObligation(LowerProp(ExpiryIr.table, ExpiryIr.env))
  private val byCode = Map(SymbolName("runExpiry") -> Substitute.Code(ExpiryIr.expireOnceRun))
  private val impl = obligations(Obligation(ObligationName.Impl,
    Prop.over(Nil, Prop.Implies(List(Hyp.of(ExpiryIr.sharesExpire)), Prop.ClaimOf(ExpiryIr.expiryJob, byCode))),
    Discharge.Auto, "Every result of expireOnce_run meets ExpiryJob, given what SharesExpire promise."))
  private val unsat = obligations(Obligation(ObligationName.Tried(TryKind.Unsat),
    Prop.over(Nil, Prop.Not(Prop.claim(ExpiryIr.expiryJob))), Discharge.Attempt(Tries.Heartbeats),
    "No world meets ExpiryJob."))

  test("ExpiryJob/Spec.lean: a flow contract's post and claim, and two obligations lowered from `Prop`") {
    val imports = List("Types", "Boundaries", "Domain.Def_sameRows", "Domain.Def_idsIn", "Domain.Def_aboutRecord",
      "Domain.Def_expireOnce_run", "Domain.Def_expireOnce", "Domain.Def_changedIds", "SharesExpire.Spec")
    val m = module("FrFlowGen.Crm.ExpiryJob.Spec", imports.map("FrFlowGen.Crm." + _), "Crm.ExpiryJob",
      post, claim, impl, unsat, Decl.MatchEqns)
    assertEquals(Print.module(m), file("ExpiryJob/Spec.lean"))
  }
