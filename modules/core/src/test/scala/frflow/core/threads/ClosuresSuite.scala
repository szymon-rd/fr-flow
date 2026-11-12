package frflow.core.threads

/** The closures of a definition, named: their numbers, and the order of the variables each captures. */
class ClosuresSuite extends munit.FunSuite:
  private def ref(name: String): Term = Term.Ref(name)
  private def closure(body: Term, captured: String*): Term =
    Term.Closure(captured.toList.map(Param(_, Ty.Nat)), body)
  private def lift(body: Term): (Decl.Definition, List[Closures.Lifted]) =
    Closures.lift(Draft.Read("f", Decl.Definition("f_2", Nil, Decl.M(Ty.Unit), body)), 0)

  test("a closure is a constructor named for its definition, whichever overload, over what it captures") {
    val (definition, lifted) = lift(Term.of("start", closure(Term.of("use", ref("b"), ref("a")), "a", "b")))
    assertEquals(definition.body, Term.of("start", Term.of("Lam_f_1", ref("b"), ref("a"))))
    assertEquals(lifted.map(_.ctor), List(Ctor("Lam_f_1", List(Param("b", Ty.Nat), Param("a", Ty.Nat)))))
    assertEquals(lifted.map(_.body), List(Decl.Definition("Lam_f_1_body", List(Param("b", Ty.Nat), Param("a", Ty.Nat),
      Param("arg", Ty.Val)), Decl.M(Ty.Val), Term.of("use", ref("b"), ref("a")))))
  }

  test("what the earlier statements mention comes first, then what the closure's body does, in its order") {
    val made = closure(Term.of("use", ref("c"), ref("a"), ref("b")), "a", "b", "c")
    val body = Term.Bind("_", Term.of("check", ref("b")), Term.Bind("_", Term.of("start", ref("c"), made),
      Term.ret(Term.unit)))
    val (_, lifted) = lift(body)
    // `b` is mentioned by a statement before; `c`, in the statement that makes the closure, is not before it
    assertEquals(lifted.map(_.ctor.params.map(_.name)), List(List("b", "c", "a")))
  }

  test("a closure inside another is numbered after it, and starts from its own body") {
    val inner = closure(Term.of("use", ref("b"), ref("a")), "a", "b")
    val outer = closure(Term.Bind("_", Term.of("check", ref("a")), Term.of("start", inner)), "a", "b")
    val (definition, lifted) = lift(Term.of("start", outer))
    assertEquals(definition.body, Term.of("start", Term.of("Lam_f_1", ref("a"), ref("b"))))
    assertEquals(lifted.map(l => l.ctor.name -> l.ctor.params.map(_.name)),
      List("Lam_f_1" -> List("a", "b"), "Lam_f_2" -> List("a", "b")))
    assertEquals(lifted.headOption.map(_.body.body), Some(Term.Bind("_", Term.of("check", ref("a")),
      Term.of("start", Term.of("Lam_f_2", ref("a"), ref("b"))))))
  }

  test("the closures of a name are numbered on from those of its other definitions") {
    val read = Draft.Read("f", Decl.Definition("f_1", Nil, Decl.M(Ty.Unit), closure(ref("a"), "a")))
    assertEquals(Closures.lift(read, 2)._2.map(_.ctor.name), List("Lam_f_3"))
  }
