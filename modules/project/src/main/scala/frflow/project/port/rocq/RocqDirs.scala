package frflow.project.port.rocq

import java.nio.file.Path

/** Where a build reads and writes: the project's `rocq/` (the generated modules and the developer's proofs, never
  * written to by a build) and FrFlow's library; everything a build writes is under `rocq/_build/`, by the name Rocq
  * loads each module by.
  */
final case class RocqDirs(project: Path, library: Path):
  /** Where Rocq is run, so what it writes beside its work (a tactic's cache) is there too. */
  val out: Path = project.toAbsolutePath.resolve(RocqDirs.Build)

  /** The source of a module a build follows: FrFlow's library's, the generated modules' and the developer's proofs';
    * none of any other (Rocq's own libraries).
    */
  def source(logical: String): Option[Path] = logical.split('.').toList match
    case "FrFlow" :: _                        => Some(library.toAbsolutePath.resolve(RocqDirs.file(logical)))
    case ("FrFlowGen" | "Proofs") :: _ :: _   => Some(project.toAbsolutePath.resolve(RocqDirs.file(logical)))
    case _                                    => None

  def compiled(logical: String): Path = out.resolve(logical.replace('.', '/') + ".vo")
  /** What the last build of the module said, with what it was a build of (`RocqCache`). */
  def said(logical: String): Path = out.resolve(logical.replace('.', '/') + ".report")
  /** The module with lemmas given up, as it is compiled then (Rocq asks a file to be named as its module is): the
    * source itself is never changed.
    */
  def scratch(logical: String): Path = out.resolve("scratch").resolve(RocqDirs.file(logical))

  /** How Rocq finds what a build compiled, from `out`. */
  def loadPath: List[String] = RocqDirs.Roots.flatMap(r => List("-Q", r, r))

object RocqDirs:
  val Build: String = "_build"
  val Roots: List[String] = List("FrFlow", "FrFlowGen", "Proofs")

  /** A module's file, as a report names it: relative to `rocq/` (the library's too). */
  def file(logical: String): String = logical.replace('.', '/') + ".v"
