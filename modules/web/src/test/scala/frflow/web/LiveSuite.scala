package frflow.web

import cats.effect.{IO, Resource}
import java.nio.file.{Files, Path}

/** The version the page polls: it moves when a file under `.frflow/` changes and when the server is started again,
  * and stays while neither happens; a supervisor is told by the environment.
  */
class LiveSuite extends munit.CatsEffectSuite:
  private val temp = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-live")))(d =>
    IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))

  private def write(d: Path, name: String, text: String): IO[Unit] = IO.blocking {
    Files.createDirectories(d.resolve(".frflow"))
    val _ = Files.writeString(d.resolve(".frflow").resolve(name), text)
  }

  temp.test("a decision written moves the version; reading twice does not; another start does") { d =>
    val live = Live("one", d, reloads = false)
    for
      empty  <- live.version
      _      <- write(d, "ledger.json", "{}")
      first  <- live.version
      again  <- live.version
      _      <- write(d, "ledger.json", """{"decisions": 1}""")
      moved  <- live.version
      other  <- Live("two", d, reloads = false).version
    yield
      assertEquals(first, again)
      assertEquals(Set(empty, first, moved, other).size, 4)
  }

  test("a supervisor is told by the environment") {
    val d = Path.of(".")
    assertEquals((Live.of("x", d, Map(Live.Reloads -> "1")).reloads, Live.of("x", d, Map.empty).reloads), (true, false))
  }
