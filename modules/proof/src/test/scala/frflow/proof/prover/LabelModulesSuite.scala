package frflow.proof.prover

import frflow.proof.rocq.LabelModules

/** The names given to what a model's statements call by a label. */
class LabelModulesSuite extends munit.FunSuite:
  private val add = "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean"
  private val four = "ox.OxError$ apply 2,ox.Supervisor,ox.ErrorMode,scala.Option,ox.ForkLocalMap:ox.OxError"
  private val six = "ox.OxError$ apply 2,ox.internal.ThreadHerd,java.lang.Object,ox.Supervisor,ox.ErrorMode," +
    "scala.Option,ox.ForkLocalMap:ox.OxError"

  test("a method is named by its class and its name, a field too, a constructor `new`; a package's by its file") {
    assertEquals(LabelModules.named(List(add, "ox.internal.ThreadHerd threads", "ox.OxError <init> :ox.OxError",
      "ox.unsupervised$package$ unsupervised 1,scala.Function1:java.lang.Object", "scala.Function apply")),
      List("Function_apply" -> "scala.Function apply", "KeySetView_add" -> add,
        "OxError_new" -> "ox.OxError <init> :ox.OxError", "ThreadHerd_threads" -> "ox.internal.ThreadHerd threads",
        "unsupervised_unsupervised" -> "ox.unsupervised$package$ unsupervised 1,scala.Function1:java.lang.Object"))
  }

  test("two of one name are told apart by how many things they take, and then by a number") {
    assertEquals(LabelModules.named(List(four, six)).map(_._1), List("OxError_apply_4", "OxError_apply_6"))
    assertEquals(LabelModules.named(List("a.B m scala.Int:scala.Unit", "a.B m scala.Long:scala.Unit")).map(_._1),
      List("B_m_1_1", "B_m_1_2"))
  }

  test("a text that is no label is left out: a sentence, a class's name, an operator") {
    assertEquals(LabelModules.named(List("Every booking ends after it starts.", "ox.internal.ThreadHerd",
      "scala.Any == java.lang.Object:scala.Boolean", "the set at a moment")), Nil)
  }
