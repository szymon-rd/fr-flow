package frflow.proof.obligation

import frflow.proof.layout.{Laid, Lowering}
import frflow.proof.layout.Handed
import frflow.proof.lean.lower.LowerKeeps
import frflow.proof.lean.print.PrintDecl

/** What `made_` states, byte for byte (`resources/always`): every result of a define meets what always holds of
  * its values (`makes_<maker>`), and what proven code hands plain Scala at each call meets it
  * (`makes_<code>_call_<i>`), each over inputs meeting every `always`.
  */
class AlwaysSuite extends munit.FunSuite:
  /** The pinned text; a missing one is written under `target/golden-obtained`, to be read and moved in. */
  private def same(path: String, printed: String): Unit =
    val pinned = scala.util.Using(scala.io.Source.fromResource(path, getClass.getClassLoader)(using
      scala.io.Codec.UTF8))(_.mkString).getOrElse {
      val to = java.nio.file.Path.of(sys.env.getOrElse("FRFLOW_GOLDEN", "modules/proof/target/golden-obtained"), path)
      java.nio.file.Files.createDirectories(to.getParent)
      fail(s"no golden $path; written to ${java.nio.file.Files.writeString(to, printed)}")
    }
    assertEquals(printed, pinned)

  /** Every `makes_` a theory's obligations declare, in the order its nodes ask them. */
  def declared(laid: Laid, r: frflow.core.analysis.resolution.Resolved): String =
    val l = Lowering(r, laid.table)
    val keeps = LowerKeeps(l.env, l.table, l.naming)
    def stated(p: Prop): List[Prop.Makes] = p match
      case m: Prop.Makes      => List(m)
      case Prop.Forall(_, b)  => stated(b)
      case Prop.Implies(_, c) => stated(c)
      case _                  => Nil
    laid.nodes.flatMap(_.required).flatMap(o => stated(o.goal)).map(m => PrintDecl(keeps.makes(m)))
      .mkString("", "\n\n", "\n")

  test("Handed: what proven code hands plain Scala at each call, through a define on the spot and another's code") {
    same("always/Handed.lean", declared(Laid(Handed.resolved, Map.empty, Nil), Handed.resolved))
  }
