package frflow.project

import java.nio.file.Files
import frflow.dsl.kb.FrModel
import frflow.proof.lean.lower.LowerObligation

/** Every obligation each port is asked, by node and name, as committed (`resources/<port>/obligations.txt`): a
  * change to the set (one gone, one more, one renamed) shows here before any Lean runs, whatever the oracle reads.
  * `FRFLOW_GOLDEN=write` writes the lists afresh, to be reviewed as any change to them is.
  */
class ObligationNamesSuite extends munit.FunSuite:
  private val examples: List[(String, FrModel)] = List("rooms" -> _root_.rooms.rooms, "auth" -> _root_.auth.knowledge,
    "crm" -> _root_.crm.knowledge, "keycloak" -> _root_.keycloak.knowledge)

  examples.foreach { (name, kb) =>
    test(s"$name: the obligations asked are the committed list") {
      val a = Projects.bare(Projects.elaborated(kb))
      val names = a.obligations.flatMap(o => (o.required ++ o.tried).map(x => s"${o.node.value} ${shown(x.name)}")) ++
        a.whole.map(x => s"Whole ${shown(x.name)}")
      val file = Projects.base.resolve(s"next/project/src/test/resources/$name/obligations.txt")
      if sys.env.get("FRFLOW_GOLDEN").contains("write") then
        Files.writeString(file, names.mkString("", "\n", "\n")): Unit
      assertEquals(names, Files.readString(file).linesIterator.toList)
    }
  }

  private def shown(n: frflow.proof.obligation.ObligationName): String = LowerObligation.name(n).text
