package frflow.project.rocq

/** The logic that proofs about threads are written in (`modules/proof/rocq/FrFlow/Jvm`): the machine as a
  * language of Iris, a rule for each of its operations proven from what the machine says the operation does, and
  * the theorem that takes a proof in the logic to every run. It needs Iris (`bin/setup-iris.sh`).
  */
class JvmLogicRocqSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  private val library = List("Threads/Prog", "Jvm/Machine", "Jvm/Lang", "Jvm/Wp", "Jvm/Rules", "Jvm/Adequacy")

  test("Rocq checks the machine's logic: each operation's rule from its step, and adequacy".tag(Rocq)) {
    assume(ThreadsRocq.hasIris, "Iris is not installed: bin/setup-iris.sh")
    assertEquals(ThreadsRocq.failing(Nil, library), None)
  }
