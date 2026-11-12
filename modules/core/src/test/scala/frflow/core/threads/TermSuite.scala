package frflow.core.threads

/** What a term mentions: the names it does not bind, in the order it first does. */
class TermSuite extends munit.FunSuite:
  private def ref(name: String): Term = Term.Ref(name)

  test("a statement binds its name in what follows, not in itself") {
    val t = Term.Bind("x", Term.of("f", ref("x"), ref("y")), Term.of("g", ref("x"), ref("z")))
    assertEquals(t.mentions, List("f", "x", "y", "g", "z"))
  }

  test("a function, a let and a tuple taken apart bind their names in their bodies") {
    val all = Term.Tuple(List("a", "c", "d", "e", "f", "g").map(ref))
    val t = Term.Let("a", ref("b"), Term.Unpack(List("c", "d"), ref("a"),
      Term.Fun(List(Binder.Typed("e", Ty.Nat), Binder.Plain("f")), all)))
    assertEquals(t.mentions, List("b", "g"))
  }

  test("an arm binds its pattern's variables, and mentions its constructors") {
    val t = Term.Match(ref("v"), List(Arm(Pattern.Ctor("VObj", List(Pattern.of("O_A", "x"))), Term.of("ret", ref("x"))),
      Arm(Pattern.Wild, ref("type_error"))))
    assertEquals(t.mentions, List("v", "VObj", "O_A", "ret", "type_error"))
  }

  test("a closure mentions what its body does, but what it is called with") {
    val t = Term.Closure(List(Param("a", Ty.Nat)), Term.of("invoke", ref("a"), ref(Term.Arg)))
    assertEquals(t.mentions, List("invoke", "a"))
  }

  test("several values held together: none is tt, one is itself") {
    assertEquals(Term.tuple(Nil), Term.unit)
    assertEquals(Term.tuple(List(ref("a"))), ref("a"))
    assertEquals(Ty.tuple(List(Ty.Nat, Ty.Exn)), Ty.Prod(List(Ty.Nat, Ty.Exn)))
    assertEquals(Ty.tuple(Nil), Ty.Unit)
  }
