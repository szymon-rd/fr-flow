package frflow.dsl.compiled.source

import frflow.core.code.ReadUnit
import java.nio.file.Paths

/** Code read for a model that speaks of its execution: the TASTy files of the place a class was compiled into,
  * each named by its path there (`ox/internal/ThreadHerd.tasty` is `ox_internal_ThreadHerd`).
  */
object ReadCode:
  /** The files whose paths, from the root of the classes, `keep` takes. */
  def of(cls: Class[?], keep: String => Boolean): List[ReadUnit] =
    val root = Option(cls.getProtectionDomain.getCodeSource).map(s => Paths.get(s.getLocation.toURI).toString)
    def relative(path: String): String = root.filter(path.startsWith).fold(path)(r => path.drop(r.length))
      .dropWhile(_ == '/')
    ReadSource.only(cls, p => keep(relative(p))).collect { case (path, tree) if keep(relative(path)) =>
      ReadUnit(relative(path).stripSuffix(".tasty").replaceAll("[^A-Za-z0-9]", "_"), tree) }
