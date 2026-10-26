package frflow.core.term.algebra

import frflow.core.term.Bound
import frflow.core.ty.Ty

/** Lists, and the operations with a body over their elements, the body a host function (LNCS 7470 §3.2: higher-order
  * abstract syntax): the interpreter that applies it decides what the variable is. `foldLeft`'s and `pairwise`'s
  * bodies have two; `nodup` is Lean's `List.Nodup`, `pairwise` its `List.Pairwise` (each element with each later one).
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
