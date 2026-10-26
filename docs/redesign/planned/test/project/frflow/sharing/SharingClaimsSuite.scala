package sharing

import frflow.core.expr.Lambda
import frflow.core.name.{KbName, SymbolName, TypeName}
import frflow.core.spec.{CallForm, FailureClause, Form, Written}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.{LowerEnv, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.Printed
import rooms.RoomsLean

/** sharing's `canViewByAccess` (read as a call of `canView`, as another is applied to the same inputs) and
  * `handleAnswers` (about a program, its failing side changing nothing; and one run stating both outcomes) in the
  * owner's forms, elaborated and printed as Lean.
  */
class SharingClaimsSuite extends munit.FunSuite:
  private val env = LowerEnv(KbName("Sharing"), _ => Nil, m => Names.builtin(m.value.stripSuffix("Model")),
    _ => Names.builtin("LibraryStore"), _ => None)
  private val naming = Naming.over(Set("access", "canView", "handle"), Set("Library", "Request", "Answer", "Failure"))

  private def failure(c: CallForm): Option[FailureClause] = c match
    case CallForm.Run(_, _, f) => f
    case CallForm.Call(_, _)   => None

  /** A post as its `def`'s value: `fun (inputs) => body`. */
  private def lean(w: Written[Lambda]): String = w.form match
    case Form.Term(t)  =>
      val (bs, body) = Printed.define(env, naming)(w.value.params, t.run)
      s"fun ${Print.binders(bs)} => ${Print.expr(body)}"
    case Form.Steps(_) => fail("a post is a term")

  test("canViewByAccess reads as a call of canView; access, applied to the same inputs, is an ordinary mention") {
    assertEquals(RoomsLean.call(canViewByAccess.statement).definition, SymbolName("canView"))
    assertEquals(lean(RoomsLean.post(canViewByAccess.statement)),
      "fun (lib : Library) (t : Int) (p : Int) (d : Int) => " +
      "((canView lib t p d) = (¬((access lib t p d) = none)))")
  }

  test("handleAnswers: a run of handle, its post over the request, the answer, before and after") {
    val c = RoomsLean.call(handleAnswers.statement)
    assertEquals((c.definition, failure(c).map(f => (f.error, lean(f.post)))), (SymbolName("handle"),
      Some((Ty.Data(TypeName("Failure")), "fun (r : Request) (error : Failure) (before : World) (after : World) => " +
        "(after = before)"))))
    assertEquals(lean(RoomsLean.post(handleAnswers.statement)),
      "fun (r : Request) (answer : Answer) (before : World) (after : World) => " +
      "((after.library = (Sharing.served before.library r)) ∧ (answer = (Sharing.answerTo before.library r)))")
  }

  test("one run with both outcomes: the success side its post, the failing side its failure clause") {
    val c = RoomsLean.call(handleKeepsOnFailure.statement)
    assertEquals(lean(RoomsLean.post(handleKeepsOnFailure.statement)),
      "fun (r : Request) (answer : Answer) (before : World) (after : World) => " +
      "(answer = (Sharing.answerTo before.library r))")
    failure(c) match
      case Some(FailureClause(e, post)) =>
        assertEquals(e, Ty.Data(TypeName("Failure")))
        assertEquals(lean(post), "fun (r : Request) (error : Failure) (before : World) (after : World) => " +
          "(after.library = before.library)")
      case other => fail(other.toString)
  }
