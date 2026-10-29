package auth

import frflow.*
import frflow.core.analysis.Problem
import frflow.core.analysis.Validate
import frflow.core.analysis.outside.Premise
import frflow.core.name.NodeId
import frflow.dsl.term.LeanType
import frflow.project.Projects
import frflow.project.pipeline.Analysis
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{ObligationName, TryKind}

/** What auth's Lean says of the values provided where the code runs (owner §21: values from outside): what always
  * holds of the session table is a hypothesis of each claim mentioning it and of each obligation binding it, so the
  * claims resting on it list `tokensIssuedOnce`; a condition's open values include what its defines reach; and the
  * root over Declarations is asked no idle try (a Declaration is no code to do nothing).
  */
class LeanShapeSuite extends munit.FunSuite:
  private val a = Projects.bare(Projects.elaborated(knowledge))

  private def module(on: Analysis, name: String): String =
    on.modules.find(_.name.dotted == s"FrFlowGen.Auth.$name").map(Print.module).getOrElse(fail(s"no module $name"))

  private def defined(text: String, name: String): String =
    text.linesIterator.dropWhile(!_.contains(s"def $name ")).take(2).mkString("\n")

  test("a claim mentioning the session table takes what always holds of it; one not mentioning it, nothing") {
    assert(defined(module(a, "grantLetsIn.Spec"), "claim").contains("((Auth.tokensIssuedOnce sessions) → (∀"),
      defined(module(a, "grantLetsIn.Spec"), "claim"))
    assert(!defined(module(a, "accessNeedsGrant.Spec"), "claim").contains("tokensIssuedOnce"))
  }

  test("every obligation binding the session table takes what always holds of it, the root's step among them") {
    val complete = defined(module(a, "accessExactly.Spec"), "complete")
    assert(complete.contains("(sessions : Sessions) (admit : String → Path → (Option UserId)), " +
      "∀ (o_sessions_0 : (Auth.tokensIssuedOnce sessions)), ∀ (h_grantTable"), complete)
  }

  test("a consistency group over the session table holds for every table meeting it, the witness taking it too") {
    val whole = module(a, "Whole")
    assert(whole.contains("∀ (sessions : Sessions), ∀ (o_sessions_0 : (Auth.tokensIssuedOnce sessions)), " +
      "∃ (signedIn"), whole)
    assert(whole.contains("fun sessions _ => ⟨"), whole)
  }

  test("a condition is over what its defines reach: grants, through grantFor") {
    val whole = module(a, "Whole")
    assert(defined(whole, "satisfiable_2_grantLetsIn").contains("∃ (sessions : Sessions) (grants : (List Grant))"),
      defined(whole, "satisfiable_2_grantLetsIn"))
  }

  test("a root over Declarations is asked no idle try: a Declaration is no code") {
    val tries = a.obligations.filter(_.node == NodeId("accessExactly")).flatMap(_.tried).map(_.name)
    assert(!tries.contains(ObligationName.Tried(TryKind.Idle)), tries)
  }

  test("a claim whose Lean takes what always holds of the session table lists the assumption saying it") {
    val unlisted = Node.claim("A request is let in only for the user its token was issued to.")(
      forall((t: Term[String], p: Term[Path]) => admit(t, p).fold(True)(u => issuedTo(t, u))))
      .refines(accessExactly)
    val kb = FrModel("Auth")((knowledge.nodes :+ unlisted)*)
      .implementProvided(grants, sessions)
      .implementTested(admit)(env => SessionStore(env(grants), env(sessions)).decide)
    val problems = Validate(Projects.elaborated(kb)).fold(_.iterator.toList, _ => Nil)
    assertEquals(problems, List(Problem.PremiseMissing(NodeId("unlisted"),
      Premise.FromOutside(LeanType[Sessions].ty), Some(NodeId("tokensIssuedOnce")))))
  }
