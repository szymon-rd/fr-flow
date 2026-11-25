package frflow.proof.prover

import frflow.core.code.Datum
import frflow.core.staged.{Arg, Handler, Kept, P, StagedCode, StagedUnit, Sym, UnitKind, V}
import frflow.proof.rocq.StagedModule

/** Staged code as the Rocq file it is printed to (`FrFlow/Code/Staged.v`). */
class StagedPrintSuite extends munit.FunSuite:
  private val check = Sym.Member("a.Herd", "check", ":scala.Unit")
  private val made = Sym.Local("$anonfun", 3)
  private val stub = Datum.Of("DefDef", List(Datum.Text("stub")))
  private def op(name: String, args: Arg*): P = P.Op(name, args.toList)
  private def value(name: String): Arg = Arg.Val(V.Var(name))

  /** `if owner ne current then stuck else ()`, on what the method is given. */
  private val checking: P = P.Bind("sc", op("captured", value("this")), P.Given(List("current_1"),
    P.Bind("held_2", op("get_field", value("this"), Arg.Text("owner")),
      P.Bind("test_3", op("ne_", value("current_1"), value("held_2")),
        P.Truth(V.Var("test_3"), P.Stuck("another thread"), P.Give(V.Unit))))))

  /** A function made, keeping a variable; and a `try` with a handler and what is run last. */
  private val making: P = P.Let("f_1", V.Function(stub, Kept(List("x#1" -> V.Var("x_1")), Some("sc"))),
    P.Handle(op("apply_", value("f_1"), Arg.Vals(Nil)),
      Some(Handler("thrown_2", "e_3", op("rethrow", value("thrown_2")))), Some(P.Give(V.Unit))))

  private val code = StagedCode(List(
    StagedUnit(UnitKind.Method(check), "m_Herd_check_1", checking),
    StagedUnit(UnitKind.Init("a.Herd"), "init_Herd_new_2", P.Give(V.Unit)),
    StagedUnit(UnitKind.Function(made), "fn_anonfun_3", making),
    StagedUnit(UnitKind.ByName(Sym.Local("<by-name>", 4)), "by_name_4", P.Give(V.Found("sc", "x#1")))),
    List("a.Herd.later" -> "a lazy value made in a method"),
    List(Sym.Member("scala.Option", "getOrElse", "1,scala.Function0:java.lang.Object") -> List(true),
      Sym.Member("java.lang.Thread", "interrupt", ":scala.Unit") -> Nil))

  private val printed = StagedModule(code)

  private def has(part: String): Unit = assert(printed.contains(part), s"not in the file:\n$part\n\n$printed")

  test("the file says how many programs it holds, and what is left to the meaning of the tree, with the reason") {
    has("(** Staged: 4 programs. Left to the meaning of the tree: 1.\n" +
      "    - a.Herd.later: a lazy value made in a method *)")
  }

  test("a method and an initialiser are given the object and the arguments; a function and an argument by name the " +
    "variables they keep") {
    has("  Definition m_Herd_check_1 (this : val) (args : list val) : D :=")
    has("  Definition init_Herd_new_2 (this : val) (args : list val) : D :=")
    has("  Definition fn_anonfun_3 (sc : scope) (args : list val) : D :=")
    has("  Definition by_name_4 (sc : scope) : D :=\n    Staged.give (Staged.found sc \"x#1\").")
  }

  test("an operation is a line: what it gave is named before it, and a truth value is taken apart") {
    has("""    sc <~ Staged.captured T this ;;
          |    match args with
          |    | [current_1] =>
          |        held_2 <~ Staged.get_field T this "owner" ;;
          |        test_3 <~ Staged.ne_ T current_1 held_2 ;;
          |        match test_3 with
          |        | VBool true =>
          |            stuck "another thread"
          |        | VBool false =>
          |            Staged.give VUnit
          |        | _ =>
          |            stuck "a condition that gave no truth value"
          |        end
          |    | _ =>
          |        stuck "a call given other than what the definition takes"
          |    end.""".stripMargin)
  }

  test("a function value holds its definition without its body, written once, and the variables it keeps") {
    has("Definition stub_1 : tree :=")
    has("    let f_1 := (VCode (Fn stub_1 ([(\"x#1\", x_1)] ++ sc)%list [])) in")
  }

  test("a try is given its body, what handles what is thrown, and what is run last") {
    has("""    Staged.try_ T
          |      (Staged.apply_ T f_1 [])
          |      (Some (fun thrown_2 e_3 =>
          |        Staged.rethrow T thrown_2))
          |      (Some
          |        (Staged.give VUnit))""".stripMargin)
  }

  test("what the staging took of each definition from outside is listed, and checked against the library") {
    has("""Definition Code_outside : list (sym * list bool) :=
          |  [((Member "scala.Option" "getOrElse" "1,scala.Function0:java.lang.Object"), [true]);
          |   ((Member "java.lang.Thread" "interrupt" ":scala.Unit"), [])].""".stripMargin)
    has("Lemma Code_outside_agrees : forallb (fun taken => Staged.takes (fst taken) (snd taken)) Code_outside = true.")
  }

  test("the units are found by what is called: a definition's name, or a class's") {
    has("  Definition Code_units : Staged.units := Staged.Units")
    has("      if sym_eqb s (Member \"a.Herd\" \"check\" \":scala.Unit\") then Some m_Herd_check_1 else")
    has("      if String.eqb cls \"a.Herd\" then Some init_Herd_new_2 else")
    has("      if sym_eqb s (Local \"$anonfun\" 3) then Some fn_anonfun_3 else")
    has("      if sym_eqb s (Local \"<by-name>\" 4) then Some by_name_4 else")
  }
