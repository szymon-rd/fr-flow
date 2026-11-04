package frflow.core.graph

import scala.annotation.tailrec

/** Walks over a graph given as a function to the vertices each leads to: each vertex once (by `key`), in an order
  * that depends only on the graph.
  */
object Walk:
  def breadthFirst[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    @tailrec def go(level: List[A], seen: Set[K], out: Vector[A]): Vector[A] =
      val fresh = level.filterNot(a => seen(key(a))).distinctBy(key)
      if fresh.isEmpty then out else go(fresh.flatMap(next), seen ++ fresh.map(key), out ++ fresh)
    go(start, Set.empty, Vector.empty).toList

  /** Each after what it leads to. A cycle is cut where it closes (`Validate` reports cycles before anything walks). */
  def postorder[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    def visit(state: (Set[K], Vector[A]), x: A, path: Set[K]): (Set[K], Vector[A]) =
      if state._1(key(x)) || path(key(x)) then state
      else
        val (done, out) = next(x).foldLeft(state)(visit(_, _, path + key(x)))
        (done + key(x), out :+ x)
    start.foldLeft((Set.empty[K], Vector.empty[A]))(visit(_, _, Set.empty))._2.toList
