package frflow.core.term.algebra

import frflow.core.term.Bound
import frflow.core.ty.Ty

/** Lists, and the operations with a body over their elements, the body a host function (LNCS 7470 §3.2: higher-order
  * abstract syntax): the interpreter that applies it decides what the variable is. `foldLeft`'s and `pairwise`'s
  * bodies have two; `nodup` is Lean's `List.Nodup`, `pairwise` its `List.Pairwise` (each element with each later one).
  * `map`, `flatMap`, `find`, `contains`, `zip` and `isEmpty` are Scala's and Lean's (`List.find?`, `x ∈ xs`).
  */
trait Lists[T[_]]:
  def nil[A](elem: Ty): T[List[A]]
  def cons[A](x: T[A], xs: T[List[A]]): T[List[A]]
  def append[A](xs: T[List[A]], ys: T[List[A]]): T[List[A]]
  def length[A](xs: T[List[A]]): T[BigInt]
  def all[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
  def any[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
  def filter[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[List[A]]
  def nodup[A](xs: T[List[A]]): T[Boolean]
  def pairwise[A](xs: T[List[A]], x: Bound[A], y: Bound[A])(p: (T[A], T[A]) => T[Boolean]): T[Boolean]
  def foldLeft[A, B](xs: T[List[A]], z: T[B], acc: Bound[B], x: Bound[A])(f: (T[B], T[A]) => T[B]): T[B]
  def map[A, B](xs: T[List[A]], x: Bound[A])(f: T[A] => T[B]): T[List[B]]
  def flatMap[A, B](xs: T[List[A]], x: Bound[A])(f: T[A] => T[List[B]]): T[List[B]]
  def find[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Option[A]]
  def contains[A](xs: T[List[A]], x: T[A]): T[Boolean]
  def zip[A, B](xs: T[List[A]], ys: T[List[B]]): T[List[(A, B)]]
  def isEmpty[A](xs: T[List[A]]): T[Boolean]

/** Finite maps (Lean's `K → Option V`): the value at a key, if any; that value or a default; the map with a key's
  * value replaced.
  */
trait Maps[T[_]]:
  def get[K, V](m: T[Map[K, V]], k: T[K]): T[Option[V]]
  def getOrElseAt[K, V](m: T[Map[K, V]], k: T[K], default: T[V]): T[V]
  def updated[K, V](m: T[Map[K, V]], k: T[K], v: T[V]): T[Map[K, V]]

/** Sets (Lean's `A → Prop`): whether a value is in one, the set with a value added, two sets' union. */
trait Sets[T[_]]:
  def member[A](s: T[Set[A]], x: T[A]): T[Boolean]
  def incl[A](s: T[Set[A]], x: T[A]): T[Set[A]]
  def union[A](s: T[Set[A]], t: T[Set[A]]): T[Set[A]]
