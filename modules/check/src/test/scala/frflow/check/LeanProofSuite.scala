package frflow
package check

import cats.effect.unsafe.implicits.global
import frflow.fixtures.*
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*
import java.nio.file.{Files, Path, Paths}

/** Proofs end to end: a knowledge base proven by automation, what root_impl rests on, a proof by hand, and
  * imports Lean builds together. End to end against Lean (see LeanLab).
  */
class LeanProofSuite extends LeanLab:

  test("the shelf is proven by automation: each node from its parts, the root from the leaves, of the code from what is trusted") {
    val kb = shelfKb.implementProven(pick)(longOnes)
    val w = workflow(kb)
    val r = w.check()
    assertEquals(statuses(r), List("OnlyGood" -> "proven", "FromList" -> "proven", "OnlyLong" -> "proven", "EveryLong" -> "proven", "Pick" -> "proven"))
    assert(r.flatMap(_._2.axioms).forall(ProofRules.allowedAxioms))
    // the root's parts make it only together: each is needed, and they do not clash
    val root = of(r, "OnlyGood")
    assertEquals(root.obligations.filter(o => o.name.lean.startsWith("needed_") || Set("complete", "clash", "unsat")(o.name.lean)).map(o => o.name.lean -> o.status.toString),
      List("complete" -> "proven", "needed_FromList" -> "not-shown", "needed_OnlyLong" -> "not-shown", "needed_EveryLong" -> "not-shown", "clash" -> "not-shown", "unsat" -> "not-shown"))
    assertEquals(result(root, "idle").map(_.status.toString), Some("not-shown"))
    // each said plainly in the snapshot's split too
    assertEquals(splitOf(w, onlyGood).needed.map(_.status), List.fill(3)(ObligationStatus.NotShown))
    assertEquals(st(splitOf(w, onlyGood), "clash"), Some("not-shown"))
    // Pick has three parents: each is proven from it, and it is proven once
    assertEquals(List(fromList, onlyLong, everyLong).map(n => st(splitOf(w, n), "complete")), List.fill(3)(Some("proven")))
    assertEquals(result(of(r, "Pick"), "impl").map(_.status.toString), Some("proven"))
    // each example is evaluated in Lean, of the contract and of the code, a define
    assertEquals(of(r, "Pick").obligations.filter(_.name.lean.startsWith("eval")).map(o => o.name.lean -> o.status.toString),
      (0 to 3).toList.flatMap(i => List(s"eval_$i", s"evalImpl_$i")).map(_ -> "proven"))
    // the code is proven: nothing is trusted
    assertEquals(result(root, "root_impl").map(r => (r.status.toString, r.detail)), Some(("proven", "the root holds of the code, trusting nothing")))
    assertEquals(w.generate.trusted, Nil)
    // the root checked alone builds the proofs of the code it composes: it does not read what a build left, or nothing
    val olean = w.ws.lean.resolve(s".lake/build/lib/lean/${w.generate.layout.impl("Pick").path.stripSuffix(".lean")}.olean")
    assert(Files.deleteIfExists(olean), olean)
    val again = of(w.check(Some("OnlyGood")), "OnlyGood")
    assertEquals(result(again, "root_impl").map(r => (r.status.toString, r.detail)), Some(("proven", "the root holds of the code, trusting nothing")))
  }

  test("two modules proving things of one match with a wildcard can be imported together: its equations are made where it is defined") {
    assume(lakeAvailable, "lake is not available")
    val dir = tempDir("sparse")
    Files.writeString(dir.resolve("lakefile.toml"),
      s"name = \"sparse\"\n\n[[require]]\nname = \"frflow\"\npath = \"$kernel\"\n\n[[lean_lib]]\nname = \"Sparse\"\nglobs = [\"Sparse.+\"]\n")
    Files.writeString(dir.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
    def file(name: String, text: String) = { Files.createDirectories(dir.resolve("Sparse")); Files.writeString(dir.resolve(s"Sparse/$name.lean"), text) }
    // As the vocabulary module declares a `define` with a wildcard case, and two nodes' modules use `grind` on it.
    val base = "import FrFlow\ninductive Req where\n  | signIn (t : String)\n  | signOut (t : String)\n  | admin (on : Bool)\n" +
      "def tokenOf : Req → Option String\n  | .signIn t => some t\n  | _ => none\nfrflow_match_eqns\n"
    def uses(b: String) = List(
      s"import Sparse.$b\ntheorem a (q : Req) (t : String) (h : tokenOf q = some t) : q = .signIn t := by\n  unfold tokenOf at h; grind\n",
      s"import Sparse.$b\ntheorem b (q : Req) (t : String) (h : tokenOf q = some t) : ∃ u, q = .signIn u := by\n  unfold tokenOf at h; grind\n")
    file("Base", base); file("A", uses("Base")(0)); file("B", uses("Base")(1)); file("C", "import Sparse.A\nimport Sparse.B\n")
    LeanLab.kernelBuilt
    val lk = lake(dir)
    val built = lk.build("Sparse.C").unsafeRunSync()
    assert(built.ok, built.output)
  }

  test("root_impl rests on what is trusted: an assumption on an operation the code calls, and a contract with plain code") {
    val kb = shelfWith(pick, shelfPort).implementProven(pick)(viaFetch).implementProven(shelfPort)(fromService, (shelf, n) => shelf.filter(_.pages >= minPages.value))
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    assertEquals(w.generate.trusted.map(_.id), List("ShelfPort"))
    val r = w.check()
    assert(r.forall(_._2.status.toString == "proven"), statuses(r))
    assertEquals(result(of(r, "OnlyGood"), "root_impl").map(_.status.toString), Some("proven"))
    // the assumption's check follows from its post, and the code beside its reference is checked against it
    val port = of(r, "ShelfPort")
    assertEquals(port.obligations.filter(o => Set("check", "impl")(o.name.lean)).map(o => o.name.lean -> o.status.toString).toSet, Set("check" -> "proven", "impl" -> "proven"))
    // Pick's code is proven from the assumption's promise alone
    assert(w.generate.obligation(pick, ObligationName.Impl).get.statement.contains("h_ShelfPort"), w.generate.obligation(pick, ObligationName.Impl))
    assertEquals(w.baseSnapshot.trusted, List(NodeId("ShelfPort")))
  }

  private val feasible = "  unfold Obl.feasible\n  exact ⟨fun x => x * x, by simp [frflow_defs]⟩"
  /** A scaffolded stub (its first steps, the goal they leave, `sorry`) replaced by a proof. */
  private def fill(src: String, o: String, proof: String) =
    src.replaceFirst(s"(?s)  unfold Obl\\.$o\n.*?  sorry\n", java.util.regex.Matcher.quoteReplacement(proof + "\n"))

  test("an obligation automation cannot prove is proven in the node's proof file, with a witness") {
    val w = workflow(squareKb)
    val first = w.check()
    assertEquals(statuses(first), List("NonNegative" -> "open", "Squares" -> "proven"))
    // automation gave up: what to write, and where, first
    assert(result(of(first, "NonNegative"), "complete").exists(_.detail.startsWith(
      "automation gave up: write theorem complete : Obl.complete in lean/Proofs/Square/NonNegative.lean (run `scaffold NonNegative`)")), of(first, "NonNegative"))
    // the goal check prints is the one the stub's first steps leave, written in the stub too
    val gaveUp = result(of(first, "NonNegative"), "complete").get.detail
    assert(gaveUp.contains("After `unfold Obl.complete; frflow_intro; simp only [frflow_defs] at *`") && gaveUp.contains("h_Squares : ∀ (x : Int), sq x = x * x"), gaveUp)
    assert(w.scaffold(nonNegative))
    val file = w.ws.lean.resolve(w.generate.layout.proofs("NonNegative").path)
    val stub = Files.readString(file)
    assert(stub.contains("  unfold Obl.complete\n  frflow_intro\n  simp only [frflow_defs] at *\n  /- The goal here") &&
      stub.contains("h_Squares : ∀ (x : Int), sq x = x * x"), stub)
    assertEquals(result(w.check(Some("NonNegative")).head._2, "complete").map(_.detail), Some("uses sorry"))

    def edit(f: String => String) = Files.writeString(file, f(Files.readString(file)))
    // from the stub's first steps, the binders by their names
    Files.writeString(file, fill(stub, "complete",
      """  unfold Obl.complete
        |  frflow_intro
        |  simp only [frflow_defs] at *
        |  intro x
        |  rw [h_Squares x]
        |  rcases Int.le_total 0 x with hx | hx
        |  · exact Int.mul_nonneg hx hx
        |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hx) (Int.neg_nonneg_of_nonpos hx)
        |    simpa [Int.neg_mul_neg] using this""".stripMargin))
    // an authored proof needs a witness that something meets the parts
    val noWitness = w.check(Some("NonNegative")).head._2
    assertEquals(result(noWitness, "feasible").map(_.status.toString), Some("open"), noWitness)
    assertEquals(st(splitOf(w, nonNegative), "complete"), Some("open"))
    edit(fill(_, "feasible", feasible))
    val proven = w.check(Some("NonNegative")).head._2
    assertEquals(st(splitOf(w, nonNegative), "complete"), Some("proven"))
    assertEquals((proven.status.toString, result(proven, "complete").map(_.detail)), ("proven", Some("authored")), proven)
    assert(!Files.readString(w.ws.lean.resolve(w.generate.layout.auto("NonNegative").path)).contains("theorem complete"))
    // a proof of something weaker does not count
    edit(src => src.replaceAll("(?s)theorem complete : Obl.complete := by.*?(?=\ntheorem feasible)", "theorem complete : True := trivial\n"))
    assertEquals(result(w.check(Some("NonNegative")).head._2, "complete").map(_.status.toString), Some("failed"))

    // Proofs may share lemmas, which are filtered and replayed like them.
    val lemmas = w.ws.lean.resolve(w.generate.layout.lemmas.path)
    def lemma(body: String) = Files.writeString(lemmas,
      s"import FrFlow\n\nnamespace Square.Lemmas\n\n$body\n\nend Square.Lemmas\n")
    lemma("""theorem sq (x : Int) : 0 ≤ x * x := by
            |  rcases Int.le_total 0 x with hx | hx
            |  · exact Int.mul_nonneg hx hx
            |  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos hx) (Int.neg_nonneg_of_nonpos hx)
            |    simpa [Int.neg_mul_neg] using this""".stripMargin)
    Files.writeString(file, fill(fill(stub.replaceFirst("import ", "import Proofs.Square.Lemmas\nimport "),
      "complete", "  unfold Obl.complete\n  intro sq h\n  simp only [frflow_defs] at *\n  intro x\n  rw [h x]\n  exact Square.Lemmas.sq x"),
      "feasible", feasible))
    val shared = w.check(Some("NonNegative")).head._2
    assertEquals((shared.status.toString, result(shared, "complete").map(_.detail)), ("proven", Some("authored")), shared)
    // a lemma file gets the same filter as a proof file
    lemma("axiom sq (x : Int) : 0 ≤ x * x")
    val bad = w.check(Some("NonNegative")).head._2
    assertEquals(bad.status.toString, "failed", bad)
    assert(bad.messages.exists(_.contains("not allowed in lean/Proofs/Square/Lemmas.lean")), bad.messages)
  }
