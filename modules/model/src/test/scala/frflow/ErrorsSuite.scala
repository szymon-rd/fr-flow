package frflow

import cats.effect.SyncIO
import frflow.fixtures.Errors
import frflow.fixtures.Errors.*
import frflow.flow.Flows

/** Errors on flows: raiseError, handleErrorWith, attempt, retry and guarantee, as Lean prints them, as they run on the
  * models (with the world's faults) and in production (an exception of a failing boundary is its error), and
  * MonadError's laws on each interpretation.
  */
class ErrorsSuite extends munit.FunSuite:
  private val num = summon[LeanType[BigInt]]
  private def lean(f: AnyRef): String = Def(Lifted.flow(f, List(num), "f"), num, Some("f"), isFlow = true).lifted.lean
  private def errorsOf(f: AnyRef): List[String] = Def(Lifted.flow(f, List(num), "f"), num, Some("f"), isFlow = true).lifted.errors
  private def steps(f: Flow[?]): Steps = Steps.of(f)._1

  test("raiseError is throwThe, handleErrorWith and attempt are tryCatchThe, retry is one try inside the other") {
    assertEquals(lean((n: Term[BigInt]) => withdraw(n)),
      """fun (n : Int) => do
        |    let b ← Vault.balance
        |    if (n > b) then
        |      throwThe Errors.VaultError Errors.VaultError.Overdrawn
        |    else
        |      Vault.put (b - n)
        |    pure (b - n)""".stripMargin)
    assertEquals(errorsOf((n: Term[BigInt]) => withdraw(n)), List("Errors.VaultError"))
    assertEquals(lean((n: Term[BigInt]) => safely(n)),
      """fun (n : Int) => do
        |    let o ← tryCatchThe Errors.VaultError (do
        |        let a ← do
        |          let b ← Vault.balance
        |          if (n > b) then
        |            throwThe Errors.VaultError Errors.VaultError.Overdrawn
        |          else
        |            Vault.put (b - n)
        |          pure (b - n)
        |        pure (Except.ok a))
        |      (fun e => do
        |        pure (Except.error e))
        |    pure (match o with | Except.error _ => 0 | Except.ok r => r)""".stripMargin)
    assertEquals(lean((n: Term[BigInt]) => deposit(n)),
      """fun (n : Int) => do
        |    tryCatchThe Errors.VaultError (do
        |        let b ← Vault.balance
        |        Vault.put (b + n))
        |      (fun _ => do
        |        Clock.sleep 1
        |        tryCatchThe Errors.VaultError (do
        |            let b_1 ← Vault.balance
        |            Vault.put (b_1 + n))
        |          (fun _ => do
        |            Clock.sleep 2
        |            let b_2 ← Vault.balance
        |            Vault.put (b_2 + n)))""".stripMargin)
  }

  test("the examples hold of the contracts and of the flows, failures included; the flows' errors are said") {
    assertEquals(Errors.kb.problems.filterNot(_.toString.contains("a root is required")), Nil)
    for n <- List[Node[?]](withdrawContract, safelyContract, depositContract, restContract) do
      val rs = Errors.kb.exampleResults(n)
      assert(rs.nonEmpty, n.id)
      assert(rs.forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), rs)
  }

  test("a flow that may fail needs a contract that says what holds when it does") {
    val p = Param[BigInt => Flow[BigInt]]("a withdrawal whose contract says nothing of failing")
    val c = Node.contract(p)("A withdrawal leaves the rest.", why = "A test.")((n, r, before, after) => r === after(VaultModel))
    val kb = KnowledgeBase("Silent", idea = "IDEA.md")(vaultKept, c).implementProven(c)((n: Term[BigInt]) => withdraw(n))
    assert(kb.problems.exists(_.toString.contains("say what holds when a run fails")), kb.problems)
  }

  test("the generated runs fail each call of a failing boundary in turn: a flow that half changes the vault is caught") {
    val sweep = Errors.kb.exampleResults(withdrawContract).filter(_.example.note.contains("failing (run on"))
    assertEquals(sweep.map(_.example.note), List(
      "three of ten, its call 1 of a failing boundary failing (run on FlakyVault)",
      "three of ten, its call 2 of a failing boundary failing (run on FlakyVault)",
      "more than it holds, its call 1 of a failing boundary failing (run on FlakyVault)"))
    assert(sweep.forall(r => r.contract == "ok" && r.implementation.contains("ok")), sweep)
    val p = Param[BigInt => Flow[Unit]]("two puts")
    val c = Node.contract(p)("Two puts leave the second.", why = "A test.")((n, r, before, after) => after(VaultModel) === n + 1)
      .failsChangingNothing[VaultError]
      .examples()(allows(BigInt(1), World(VaultModel -> BigInt(0)), (), World(VaultModel -> BigInt(2)), "both"),
        forbids(BigInt(1), World(VaultModel -> BigInt(0)), (), World(VaultModel -> BigInt(1)), "not the first"))
    val kb = KnowledgeBase("Twice", idea = "IDEA.md")(vaultKept, c).implementProven(c)((n: Term[BigInt]) => vault.put(n) *> vault.put(n + 1))
    val half = kb.exampleResults(c).filter(_.example.note.contains("call 2"))
    assertEquals(half.map(_.contract), List("the run fails with Down and leaves World(VaultModel = 1), which the contract forbids"))
  }

  /** The three interpretations: on the model with faults, on the vault's code now, and on it in SyncIO. Each gives the
    * outcome and what the vault holds after.
    */
  private val interpretations: List[(String, (Flow[?], BigInt, List[Boolean]) => (Either[Any, Any], BigInt))] = List(
    "on the model" -> { (f, held, faults) =>
      try { val (r, w) = Flows.onModels(steps(f), Map.empty, World(VaultModel -> held, ClockModel -> ClockState(0, Nil)).failing(faults*)); (Right(r), w(VaultModel)) }
      catch case Flows.Raised(e, w) => (Left(e), w(VaultModel)) },
    "on the vault's code" -> { (f, held, faults) =>
      val v = FlakyVault(held, faults)
      val r = try Right(Flows.runNow(steps(f), Map.empty, Map(vault -> v, Clock.boundary -> FakeClock(0)))) catch case FlowFailed(e) => Left(e)
      (r, v.amount) },
    "in SyncIO" -> { (f, held, faults) =>
      val v = FlakyVault(held, faults)
      val r = Flows.run[SyncIO](steps(f), Map.empty, Map(vault -> v, Clock.boundary -> FakeClock(0)), Nil).attempt.unsafeRunSync()
        .left.map { case FlowFailed(e) => e; case x => throw x }
      (r, v.amount) })

  test("the error operations run the same on the model, on the vault's code and in SyncIO") {
    def n(x: Int): Term[BigInt] = Term.lit(BigInt(x))
    def same(f: Flow[?], held: BigInt, faults: List[Boolean], expected: (Either[Any, Any], BigInt)) =
      interpretations.foreach((how, run) => assertEquals(run(f, held, faults), expected, how))
    same(withdraw(n(3)), 10, Nil, (Right(BigInt(7)), BigInt(7)))
    same(withdraw(n(30)), 10, Nil, (Left(VaultError.Overdrawn), BigInt(10)))
    same(withdraw(n(3)), 10, List(false, true), (Left(VaultError.Down), BigInt(10)))
    same(safely(n(3)), 10, List(true), (Right(BigInt(0)), BigInt(10)))
    same(deposit(n(5)), 10, List(true, false, true), (Right(()), BigInt(15)))
    same(deposit(n(5)), 10, List(true, true, true), (Left(VaultError.Down), BigInt(10)))
    same(depositThenRest(n(5)), 10, List(true), (Left(VaultError.Down), BigInt(10)))
    same(Flow.bracket[VaultError](vault.balance)(b => vault.put(b + 1))(b => vault.put(b + 100)), 10, List(false, true), (Left(VaultError.Down), BigInt(110)))
  }

  test("MonadError's laws hold on the model, on the vault's code and in SyncIO, on generated inputs and faults") {
    val rnd = scala.util.Random(3)
    val err: Term[VaultError] = VaultError.Overdrawn
    def g(x: Term[BigInt]): Flow[BigInt] = vault.put(x).as(x)
    for _ <- 1 to 100 do
      val a = BigInt(rnd.between(-5, 6))
      val held = BigInt(rnd.between(-5, 6))
      val faults = List.fill(rnd.between(0, 4))(rnd.nextBoolean())
      val fa: Flow[BigInt] = vault.balance.flatMap(b => g(b + a))
      val laws: List[(String, Flow[?], Flow[?])] = List(
        ("raiseError then handleErrorWith is the handler", Flow.raiseError[BigInt](err).handleErrorWith[VaultError](e => g(Term.lit(a))), g(Term.lit(a))),
        ("pure then handleErrorWith is pure", Flow.pure(Term.lit(a)).handleErrorWith[VaultError](_ => g(Term.lit(a + 1))), Flow.pure(Term.lit(a))),
        ("raiseError then flatMap is raiseError", Flow.raiseError[BigInt](err).flatMap(g), Flow.raiseError[BigInt](err)),
        ("handleErrorWith raiseError is the flow", fa.handleErrorWith[VaultError](e => Flow.raiseError[BigInt](e)), fa),
        ("attempt folded is handleErrorWith", fa.attempt[VaultError].map(o => o.fold(_ => Term.lit(a), x => x)),
          fa.handleErrorWith[VaultError](_ => Flow.pure(Term.lit(a)))))
      for (law, l, r) <- laws; (how, run) <- interpretations do
        assertEquals(run(l, held, faults), run(r, held, faults), s"$law $how, $a, $held held, faults $faults")
  }
