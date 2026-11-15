package frflow.runs.code

import frflow.{Call as _, *}
import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.project.Projects
import frflow.runs.*

/** Code written in a statement is read as the call it is: named as the tree read from its TASTy names the method,
  * taking the statement's terms and constants in order, what it is called on first.
  */
class CodeSuite extends munit.FunSuite:
  private def free[A: RocqType](i: Int): Term[A] = Term.free[A](Binder(VarId.level(i), "v", RocqType[A].ty))
  private val t = free[Ref[Thread]](0)
  private val s = free[Ref[Threads]](1)
  private val till = free[Ref[Till]](2)
  private val item = free[Ref[Item]](3)

  /** What a call names, and how many things it takes. */
  private def read[A](call: Stating ?=> Call[A]): (String, Int) =
    var seen = Option.empty[(String, Int)]
    val probe = Node.claim("A statement that reads the call.") {
      val c = call
      seen = Some((c.what, c.takes.length))
      True
    }
    assert(FrModel("Probe")(probe).elaborated.isValid)
    seen.getOrElse(fail("the statement was not read"))

  test("a method of the JDK is named by its declarer, name and signature") {
    assertEquals(read(started(t)), ("java.lang.Thread start :scala.Unit", 1))
    assertEquals(read(added(s, t))._2, 2)
    assert(read(added(s, t))._1.endsWith(" add java.lang.Object:scala.Boolean"), read(added(s, t))._1)
    assertEquals(read(asked(s)),
      ("java.util.concurrent.ConcurrentHashMap$.CollectionView isEmpty :scala.Boolean", 1))
  }

  test("a method of an object of the JDK is called on no object of the statement") {
    assertEquals(read(current), ("java.lang.Thread$ currentThread :java.lang.Thread", 0))
  }

  test("a method takes what it is called on, then objects and data, terms or constants") {
    val times = free[BigInt](4)
    assertEquals(read(rung(till, item, times)),
      ("frflow.runs.code.Till ring frflow.runs.code.Item,scala.Int:scala.Boolean", 3))
    assertEquals(read(rungTwice(till, item))._2, 3)
  }

  test("a constructor and a function of a package are calls, with what they are given in every list") {
    assertEquals(read(made(free[String](5)))._1, "frflow.runs.code.Till <init> java.lang.String:frflow.runs.code.Till")
    assertEquals(read(closed(till, till)),
      ("frflow.runs.code.Shop$package$ closeAll frflow.runs.code.Till,scala.Boolean,frflow.runs.code.Till:scala.Int",
        3))
  }

  test("code followed by a word of a call is read as the call, in the statement's Rocq") {
    val files = Projects.bare(Projects.elaborated(written)).rocq.files
    val text = files.map(_._2).mkString("\n")
    assert(text.contains("""(Invocation_mk "java.lang.Thread start :scala.Unit"%string [t])"""), text)
    assert(text.contains("(Answer_Returned (Thing_Truth (~ (wasIn))))"), text)
  }

