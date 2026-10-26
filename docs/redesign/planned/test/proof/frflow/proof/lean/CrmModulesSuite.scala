package frflow.proof.lean

import frflow.core.name.SymbolName
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{LowerObligation, LowerProp}
import frflow.proof.lean.print.*
import frflow.proof.obligation.*
import L.*

/** Four modules of `examples/crm/lean/FrFlowGen/Crm` (copied into the resources) print byte for byte from their AST;
  * the post of `ExpiryJob` and the steps of `expireOnce` are lowered from the IR (`ExpiryIr`).
  */
class CrmModulesSuite extends munit.FunSuite:
  private def file(path: String): String =
    scala.io.Source.fromResource(s"crm/$path", getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  private val crmStore = n("CrmStore")
  private val world = n("World")
  private val expireType = arrows(crmStore, n("Int"), crmStore)
  private def stateM(s: String, r: String) = app(n("StateM"), n(s), n(r))
  private def dots(on: String, fields: String*) = fields.foldLeft(n(on))(LExpr.Dot(_, _))

  private val database = Decl.Documented(
    "The boundary database: the SQLite database the CRM keeps its records, shares, expiries and event log in.",
    Decl.Class(nm("Database"), List(x("m", arrows(n("Type"), n("Type")))), List(
      nm("load") -> app(n("m"), crmStore),
      nm("logEvent") -> arrows(n("Event"), app(n("m"), n("Unit"))),
      nm("storeAbout") -> arrows(n("Int"), crmStore, app(n("m"), n("Unit"))))))

  private def modify(v: String, body: LExpr) =
    DoLine.Step(app(n("modify"), par(LExpr.Fun(List(LBinder.Bare(nm(v))), body))))
  private def tablesMk(store: LExpr, events: LExpr) = par(app(c("Tables.mk"), store, events))
  private val logEvent = tablesMk(dots("t", "store"),
    par(LExpr.Infix(LOp.Append, dots("t", "events"), LExpr.ListLit(List(n("e"))))))
  private val storeAbout = tablesMk(
    par(app(c("Crm.replaceAbout"), dots("t_1", "store"), n("id_"), par(app(c("Crm.aboutRecord"), n("t"), n("id_"))))),
    dots("t_1", "events"))
  private val model = Decl.Namespace(ns("DatabaseModel"), List(
    Decl.Def(defs, nm("load"), Nil, stateM("Tables", "CrmStore"),
      LExpr.Do(List(DoLine.Bind(nm("t"), n("get")), DoLine.Step(app(n("pure"), dots("t", "store")))), 4)),
    Decl.Def(defs, nm("logEvent"), Nil, arrows(n("Event"), stateM("Tables", "Unit")),
      LExpr.Fun(List(x("e", n("Event"))), LExpr.Do(List(modify("t", logEvent)), 4))),
    Decl.Def(defs, nm("storeAbout"), Nil, arrows(n("Int"), crmStore, stateM("Tables", "Unit")),
      LExpr.Fun(List(x("id_", n("Int")), x("t", crmStore)), LExpr.Do(List(modify("t_1", storeAbout)), 4)))))

  private val worldDecl = Decl.Documented("The models' states: what proven flows run on.",
    Decl.Structure(nm("World"), List(nm("database") -> n("Tables"))))

  private def onWorld(op: String, args: String*) = within("database", app(c(s"DatabaseModel.$op"), args.map(n)*))
  private val instance = Decl.Instance(app(n("Database"), par(app(n("StateM"), world))), List(
    InstanceField(nm("load"), Nil, onWorld("load")),
    InstanceField(nm("logEvent"), List(nm("e")), onWorld("logEvent", "e")),
    InstanceField(nm("storeAbout"), List(nm("id_"), nm("t")), onWorld("storeAbout", "id_", "t"))))

  private def lemma(op: String, params: List[(String, LExpr)], result: String) =
    Decl.Theorem(defs, nm(s"Database.${op}_onWorld"), params.map(x(_, _)),
      LExpr.Infix(LOp.Eq, LExpr.Typed(par(app(c(s"Database.$op"), params.map(p => n(p._1))*)), stateM("World", result)),
        onWorld(op, params.map(_._1)*)), Proof.Rfl, Break.NextLine)

  test("Boundaries.lean: the class, the model, World, the instance and its lemmas") {
    val imports = List("Types", "Domain.Def_replaceAbout", "Domain.Def_aboutRecord").map("FrFlowGen.Crm." + _)
    val m = module("FrFlowGen.Crm.Boundaries", imports, "Crm",
      database, model, worldDecl, instance, lemma("load", Nil, "CrmStore"),
      lemma("logEvent", List("e" -> n("Event")), "Unit"),
      lemma("storeAbout", List("id_" -> n("Int"), "t" -> crmStore), "Unit"))
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
    val d = Decl.Def(defs, nm("expireOnce_run"), List(x("expire", expireType)),
      arrows(n("Int"), world, par(times(crmStore, world))),
      LExpr.Fun(List(x("now", n("Int")), x("w", world)),
        par(app(c("FrFlow.runOn"), par(app(par(app(c("Crm.expireOnce"), n("expire"))), n("now"))), n("w")))))
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
