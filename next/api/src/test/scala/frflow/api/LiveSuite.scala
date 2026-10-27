package frflow.api

import cats.effect.{IO, Resource}
import frflow.api.view.{Stop, Warning}
import frflow.api.node.lean.ObligationState
import frflow.core.consistency.Vacuity
import frflow.project.Live
import frflow.proof.layout.LeanWorkspace
import java.nio.file.{Files, Path}

/** The live API over a project's directory (a fresh one, outside git, with no key there): read and rendered on disk,
  * and checked by Lean with FrFlow's library. Tagged `Lean`: `sbt Lean/test` runs it, plain `sbt test` does not.
  */
class LiveSuite extends munit.CatsEffectSuite:
  private val dir = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-api")))(d =>
    IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))

  private def env(d: Path) = Map("HOME" -> d.toString, "FRFLOW_KEY" -> d.resolve("no.key").toString)

  dir.test("on disk: the view warns of no key, render writes the Lean, who decides stops on the key".tag(Live)) {
    d => FrFlowApi.make(Opened.before, d, env(d)).use { api =>
      for
        view     <- api.reading.view
        rendered <- api.proving.render
        who      <- api.deciding.developer(None).attempt
      yield
        assert(view.warnings.contains(Warning.NoKey), view.warnings)
        assert(rendered.nonEmpty && Files.isRegularFile(d.resolve("lean/lakefile.toml")))
        assertEquals(who.left.map(_.getClass), Left(classOf[Stop.NoKey]))
    }
  }

  dir.test("with an empty env there is no key: none is read from the real home; who decides stops".tag(Live)) {
    d => FrFlowApi.make(Opened.before, d, Map.empty).use { api =>
      for
        view <- api.reading.view
        who  <- api.deciding.developer(None).attempt
      yield
        assert(view.warnings.contains(Warning.NoKey), view.warnings)
        assertEquals(who, Left(Stop.NoKey("FRFLOW_KEY (or HOME) not set")))
    }
  }

  dir.test("Lean, with the library a project requires, shows an implication's condition can hold".tag(Live)) { d =>
    assert(LeanWorkspace.libraryBuilt._1, LeanWorkspace.libraryBuilt._2)
    FrFlowApi.make(Opened.before.copy(library = LeanWorkspace.library), d, env(d)).use { api =>
      Opened.checked(api.proving.check(None)).map { v =>
        val possible = v.whole.possible.collect { case (Vacuity.Satisfiable(n, _, _), o) => n.value -> o.state }
        assertEquals(possible, List("sameAbove" -> ObligationState.Proven), v.whole.possible.toString)
      }
    }
  }
