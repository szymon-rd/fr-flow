package frflow.proof.rocq.threads

import frflow.core.threads.{Arm, Binder, Pattern, Term, Ty}
import frflow.proof.rocq.threads.PrintTerm.{Bars, Place}

/** Rocq's text of a term: the parentheses Rocq needs, and no other. */
class PrintTermSuite extends munit.FunSuite:
  private given Bars = Bars.Leading
  private def ref(name: String): Term = Term.Ref(name)
  private def flat(t: Term): String = PrintTerm.flat(t, Place.Top)

  test("an argument that is not a name is in parentheses; a program bound is, unless an application or a match") {
    assertEquals(flat(Term.of("call", Term.of("AbGet", Term.of("f", ref("this"))))), "call (AbGet (f this))")
    assertEquals(flat(Term.Bind("_", Term.If(ref("c"), ref("a"), ref("b")), ref("k"))),
      "_ <- (if c then a else b) ;; k")
    assertEquals(flat(Term.Bind("x", Term.of("call", ref("CfNew")), Term.ret(ref("x")))), "x <- call CfNew ;; ret x")
    assertEquals(flat(Term.If(ref("c"), Term.Bind("_", ref("m"), ref("k")), ref("b"))), "if c then _ <- m ;; k else b")
  }

  test("an integer is in Z's scope, but as an operand of Z.eqb; an empty list or a null has its type") {
    assertEquals(flat(Term.of("AiNew", Term.Num(0))), "AiNew 0%Z")
    assertEquals(flat(Term.of("Z.eqb", ref("v"), Term.Num(0))), "Z.eqb v 0")
    assertEquals(flat(Term.ret(Term.At("nil", Ty.Exn))), "ret (@nil exn)")
    assertEquals(flat(Term.of("VList", Term.Items(Nil))), "VList []")
    assertEquals(flat(Term.of("f", Term.of("cons", ref("e"), ref("es")))), "f (e :: es)")
  }

  test("a function's binders: typed, the one of a loop bare, a handler's with no type") {
    val state = Ty.Prod(List(Ty.list(Ty.Tid), Ty.option(Ty.Exn)))
    assertEquals(flat(Term.Fun(List(Binder.Typed("x", Ty.Tid), Binder.Typed("st", Ty.Unit)), ref("m"))),
      "fun (x : tid) (st : unit) => m")
    assertEquals(flat(Term.Fun(List(Binder.Bare("st", state)), ref("m"))), "fun st : list tid * option exn => m")
    assertEquals(flat(Term.of("try_catch", ref("m"), Term.Fun(List(Binder.Plain("e")), ref("h")))),
      "try_catch m (fun e => h)")
    assertEquals(PrintTerm.ty(Ty.Of("M", Ty.Sum(Ty.Exn, Ty.Val))), "M (exn + val)")
  }

  test("a match has a bar before each arm where the definitions are written, none before the first in a cast") {
    val t = Term.Match(ref("v"), List(Arm(Pattern.Ctor("VObj", List(Pattern.of("O_A", "x"))), Term.ret(ref("x"))),
      Arm(Pattern.Wild, ref("type_error"))))
    assertEquals(flat(t), "match v with | VObj (O_A x) => ret x | _ => type_error end")
    assertEquals(PrintTerm.flat(t, Place.Top)(using Bars.Inner),
      "match v with VObj (O_A x) => ret x | _ => type_error end")
  }

  test("statements each start a line, what follows them at the same margin") {
    val t = Term.Bind("x", Term.of("call", ref("CfNew")), Term.Let("y", ref("x"), Term.ret(ref("y"))))
    assertEquals(PrintTerm.lines(t, Place.Top, 2), "x <- call CfNew ;;\n  let y := x in\n  ret y")
  }
