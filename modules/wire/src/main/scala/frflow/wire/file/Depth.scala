package frflow.wire.file

import io.circe.Json

/** How deep a document nests, looked at only down to `limit`, so the walk itself stays shallow: the codecs recurse
  * once per level, and a file nested deeper (a value in a counterexample) would overflow the stack reading it.
  */
object Depth:
  val limit: Int = 256

  /** The path of the first value nested deeper than `limit`, from the document's root (`.a.b[0]`). */
  def beyond(j: Json): Option[String] = walk(j, 0, "")

  private def walk(j: Json, depth: Int, path: String): Option[String] =
    if depth > limit then Some(path)
    else j.arrayOrObject(None,
      xs => first(xs.iterator.zipWithIndex.map((x, i) => walk(x, depth + 1, s"$path[$i]"))),
      o => first(o.toIterable.iterator.map((k, v) => walk(v, depth + 1, s"$path.$k"))))

  private def first(paths: Iterator[Option[String]]): Option[String] = paths.collectFirst { case Some(p) => p }
