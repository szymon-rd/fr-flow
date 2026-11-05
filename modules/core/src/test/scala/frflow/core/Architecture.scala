package frflow.core

/** What `ArchitectureSuite` finds in a source, each rule a function of the files, so its own tests can seed one. */
object Architecture:
  /** Effects, JSON, files, randomness and the environment: banned in the pure modules. */
  val Impure = ("""cats\.effect|io\.circe|java\.nio\.file\.(Files\b|\*|\{[^}]*\bFiles\b)|\bRandom\b|""" +
    """System\.(getenv|getProperty|getProperties)|\bsys\.(env|props)\b""").r
  /** A lock: a mutex, a semaphore, a monitor, an atomic or a lock of the JDK's. */
  val Lock = """\bMutex\b|\bSemaphore\b|\bsynchronized\b|java\.util\.concurrent\.(atomic|locks)\b""".r

  def impure(f: Source): List[String] = Impure.findAllIn(f.code).toList.distinct.map(m => s"${f.rel}: $m")
  def locks(f: Source): List[String] = Lock.findAllIn(f.code).toList.distinct.map(m => s"${f.rel}: $m")

  /** What a module's sources name of another module that `edges` does not let it. */
  def crossing(files: List[Source], edges: Map[String, List[String]]): List[String] =
    files.flatMap(f => f.refs.filter(r => r.module != f.module).filterNot(r =>
      edges.getOrElse(f.module, Nil).exists(e => r.within(e))).map(r => s"${f.rel}: ${r.path}")).distinct
