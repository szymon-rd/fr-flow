package frflow.project.rocq

import frflow.core.threads.{Assemble, Draft}
import frflow.dsl.compiled.Inspect
import frflow.dsl.compiled.threads.ReadThreads
import frflow.dsl.compiled.threads.known.ThreadUnit
import frflow.dsl.compiled.threads.known.ThreadUnit.{Group, Kind, Member}
import frflow.proof.rocq.threads.RocqThreads

/** The reader of thread programs on a class of this suite's own (`Gate`): the rules Ox's code does not come to,
  * and what is refused, each definition as the Rocq it is printed as.
  */
class GateRocqSuite extends munit.FunSuite:
  private val gate = "frflow.project.rocq.Gate"
  private val unit = ThreadUnit(List(Kind.Class(gate)), List(Group(gate, List(Member.Whole(gate)))), Nil, gate)
  private lazy val draft: Draft = Inspect(classOf[Gate])(q => ReadThreads(q, unit))
  private lazy val file: String = RocqThreads.file(Assemble(draft), "A gate.")

  /** The definition `name` of the file, as its sentence. */
  private def definition(name: String): String =
    RocqText.sentences(file).find(_.startsWith(s"Definition $name ")).getOrElse(fail(s"no definition $name"))

  private def sentence(text: String): String = RocqText.sentences(text).mkString

  test("a var through a while: the loop gives its new value, the condition's effect is the loop's test") {
    assertEquals(definition("Gate_drain"), sentence(
      """Definition Gate_drain (this : Gate) : M Z :=
        |  let left := 0%Z in
        |  left <- while (fun left : Z => call (AbGetAndSet (Gate_open this) false))
        |    (fun left : Z => call (AiDecrementAndGet (Gate_passed this))) left ;;
        |  ret left.""".stripMargin))
  }

  test("two effects among the arguments of a call are run in order, and named x1 and x2") {
    assertEquals(definition("Gate_swap"), sentence(
      """Definition Gate_swap (this : Gate) : M bool :=
        |  x1 <- call (AbGetAndSet (Gate_open this) false) ;;
        |  x2 <- call (AbGet (Gate_open this)) ;;
        |  Gate_both this x1 x2.""".stripMargin))
  }

  test("a value that may be null, read after another effect, is unnull where it is read") {
    assertEquals(definition("Gate_after"), sentence(
      """Definition Gate_after (this : Gate) : M bool :=
        |  gate <- call (ArGet (Gate_next this)) ;;
        |  _ <- call (AbSet (Gate_open this) true) ;;
        |  x <- unnull gate ;;
        |  x <- cast_Gate x ;;
        |  Gate_swap x.""".stripMargin))
  }

  test("a return that ends a branch is the branch; a value dropped is bound to nothing") {
    assertEquals(definition("Gate_admit"), sentence(
      """Definition Gate_admit (this : Gate) : M bool :=
        |  x <- call (AbGet (Gate_open this)) ;;
        |  if negb x then ret false else _ <- call (AiIncrementAndGet (Gate_passed this)) ;; ret true.""".stripMargin))
  }

  test("what the rules do not read is chaos named for its method, and the reason is kept") {
    assertEquals(draft.unread.map(_.what), List(s"$gate.name", s"$gate.stamp", s"$gate.shadow", s"$gate.twice"))
    assertEquals(definition("Gate_stamp"), sentence(
      s"""Definition Gate_stamp (this : Gate) : M Z := chaos "$gate.stamp"."""))
    assert(!file.contains("Gate_name"), "a method whose result is of a type that is not read has no definition")
    assert(draft.unread.map(_.why).mkString("; ").contains("a variable named call"), draft.unread)
    assert(draft.unread.map(_.why).mkString("; ").contains("a return that does not end its method"), draft.unread)
  }

  test("Rocq reads the gate's file".tag(Rocq)) {
    assertEquals(ThreadsRocq.failing(List("Gate/Gen.v" -> file)), None)
  }
