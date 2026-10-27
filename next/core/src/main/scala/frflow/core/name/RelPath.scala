package frflow.core.name

/** A path relative to the project's directory, normalized (`src/main/scala/auth/Server.scala`): the same in every
  * checkout. Built only through `parse`, so a `RelPath` is never absolute and never leaves the project.
  */
opaque type RelPath = String

object RelPath:
  enum Invalid:
    case Absolute(path: String)
    case OutsideProject(path: String)
    case Empty

  def parse(s: String): Either[Invalid, RelPath] =
    val p = java.nio.file.Path.of(s).normalize
    if s.trim.isEmpty then Left(Invalid.Empty)
    else if p.isAbsolute then Left(Invalid.Absolute(s))
    else if p.startsWith("..") then Left(Invalid.OutsideProject(s))
    else Right(p.toString.replace('\\', '/'))

  /** `dir/rel` for a path FrFlow makes from identifiers (a Lean module's file): never absolute, never `..`. */
  def fromIdentifiers(dir: String, rel: String): RelPath = s"$dir/$rel"

  extension (p: RelPath)
    def value: String = p
    def isUnder(dir: RelPath): Boolean = p == dir || p.startsWith(dir + "/")
    /** The file's name without its extension (`DecisionContract` of `…/DecisionContract.lean`). */
    def stem: String = p.split('/').last.takeWhile(_ != '.')
  given Ordering[RelPath] = Ordering.String
