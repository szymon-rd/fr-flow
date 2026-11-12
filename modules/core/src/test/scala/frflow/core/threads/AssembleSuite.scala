package frflow.core.threads

import frflow.core.threads.Draft.{Group, Read}

/** A unit read, laid out as a file: the order of its definitions, and what of its support it holds. */
class AssembleSuite extends munit.FunSuite:
  private def definition(name: String, body: Term): Decl.Definition = Decl.Definition(name, Nil, Decl.M(Ty.Unit), body)
  private def read(name: String, calls: String*): Read =
    Read(name, definition(name, calls.foldRight(Term.ret(Term.unit))((c, rest) => Term.Bind("_", Term.Ref(c), rest))))
  private def draft(groups: List[Group], support: Support): Draft = Draft(Nil, groups, support, Ty.Nat, Nil)
  private val none = Support(Nil, Nil, Nil, Nil, Nil)
  private def names(p: Program): List[String] = p.sections.flatMap(_.defs).map(_.name)

  test("a group keeps its order, but a definition is written after those of the group it calls") {
    val group = Group("g", List(read("a", "b", "d"), read("b"), read("c", "a"), read("d", "b")))
    assertEquals(names(Assemble(draft(List(group), none))), List("b", "d", "a", "c"))
  }

  test("a pass writes every definition whose callees are written, those written earlier in the pass among them") {
    val group = Group("g", List(read("start", "check", "verify"), read("check"), read("verify", "check"), read("last")))
    assertEquals(names(Assemble(draft(List(group), none))), List("check", "verify", "last", "start"))
  }

  test("groups keep their order, and a definition that calls itself is written") {
    val groups = List(Group("one", List(read("x", "x"))), Group("two", List(read("y", "x"))))
    assertEquals(names(Assemble(draft(groups, none))), List("x", "y"))
  }

  test("the file holds the globals, casts and cases of obj its definitions mention, in the order they first do") {
    val cast = definition("cast_A", Term.of("O_A"))
    val option = definition("cast_option_A", Term.of("cast_A"))
    val support = Support(List(Ctor("O_Shared", Nil)), List(Ctor("O_B", Nil), Ctor("O_A", Nil), Ctor("O_Unused", Nil)),
      List(definition("late", Term.Ref("0")), definition("early", Term.Ref("0")), definition("unused", Term.Ref("0"))),
      List(option, definition("cast_list", Term.unit), cast), Nil)
    val group = Group("g", List(read("f", "early", "cast_list", "O_B"), read("g", "late", "cast_option_A")))
    val program = Assemble(draft(List(group), support))
    // a cast that calls another is written directly after it, though it is mentioned later
    assertEquals(program.support.map(_.name), List("early", "late", "cast_list", "cast_A", "cast_option_A"))
    assertEquals(program.types,
      List(Decl.Inductive("obj", List(Ctor("O_Shared", Nil), Ctor("O_B", Nil), Ctor("O_A", Nil)))))
  }

  test("of the methods of a class not read, the file holds those its definitions call, in the class's order") {
    val externs = Section("E: not read", List(definition("E_a", Term.unit), definition("E_b", Term.unit),
      definition("E_c", Term.unit)))
    val program = Assemble(draft(List(Group("g", List(read("f", "E_c", "E_a")))), none.copy(externs = List(externs))))
    assertEquals(program.externs.flatMap(_.defs).map(_.name), List("E_a", "E_c"))
  }
