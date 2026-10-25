package frflow.protocol

import scala.annotation.tailrec

/** Walks over a graph given as a function to the vertices each leads to: each vertex once (by `key`), in an
  * order that depends only on the graph.
  */
object Walk:
  /** `start`, then what it leads to, level by level. */
  def breadthFirst[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    @tailrec def go(level: List[A], seen: Set[K], out: Vector[A]): Vector[A] =
      val fresh = level.filterNot(a => seen(key(a))).distinctBy(key)
      if fresh.isEmpty then out else go(fresh.flatMap(next), seen ++ fresh.map(key), out ++ fresh)
    go(start, Set.empty, Vector.empty).toList

  /** Depth first, each before what it leads to. */
  def preorder[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    def go(xs: List[A], state: (Set[K], Vector[A])): (Set[K], Vector[A]) =
      xs.foldLeft(state) { case ((seen, out), x) =>
        if seen(key(x)) then (seen, out) else go(next(x), (seen + key(x), out :+ x))
      }
    go(start, (Set.empty, Vector.empty))._2.toList

  /** Each after what it leads to (dependencies first). A cycle is cut where it closes: the vertex that
    * closes it comes after the others.
    */
  def postorder[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    def visit(state: (Set[K], Vector[A]), x: A, path: Set[K]): (Set[K], Vector[A]) =
      val k = key(x)
      if state._1(k) || path(k) then state
      else
        val (done, out) = next(x).foldLeft(state)(visit(_, _, path + k))
        (done + k, out :+ x)
    start.foldLeft((Set.empty[K], Vector.empty[A]))(visit(_, _, Set.empty))._2.toList
