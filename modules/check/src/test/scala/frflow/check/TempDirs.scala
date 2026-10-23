package frflow
package check

import java.nio.file.{Files, Path}
import java.util.Comparator
import java.util.concurrent.ConcurrentLinkedQueue
import scala.util.Using

/** Temporary directories for a suite's tests, each deleted when its test ends. */
trait TempDirs extends munit.FunSuite:
  private val made = ConcurrentLinkedQueue[Path]()

  def tempDir(prefix: String): Path =
    val dir = Files.createTempDirectory(prefix)
    made.add(dir)
    dir

  override def afterEach(context: AfterEach): Unit =
    Iterator.continually(made.poll()).takeWhile(_ != null).foreach(dir =>
      Using.resource(Files.walk(dir))(_.sorted(Comparator.reverseOrder).forEach(Files.delete(_))))
    super.afterEach(context)
