package frflow
package term

import frflow.types.Shape

/** Values holding terms (`List(a, b)`, `Some(u)`, `(a, b)`) are terms; a plain value (`Nil`, `None`) is one first. */
private[frflow] trait TermsOfValues:
  given someTerm[A]: Conversion[Some[Term[A]], Term[Option[A]]] = s => some(s.value)
  given listTerm[A](using a: LeanType[A]): Conversion[List[Term[A]], Term[List[A]]] =
    l => Term(Tree.ListT(l.map(_.termTree)), LeanType.of(Shape.ListOf(l.headOption.fold(a)(_.termType))))
  given pairTerm[A, B]: Conversion[(Term[A], Term[B]), Term[(A, B)]] = pair(_)
  given pairsTerm[A, B](using a: LeanType[A], b: LeanType[B]): Conversion[List[(Term[A], Term[B])], Term[List[(A, B)]]] =
    ps => Term(Tree.ListT(ps.map(pair(_).termTree)), LeanType.of(Shape.ListOf(LeanType.of(Shape.TupleOf(List(a, b))))))
  /** A pair of terms equals a pair: `(booked, after) === when(c)((True, held :+ request)).otherwise((False, held))`. */
  extension [A, B](p: (Term[A], Term[B])) def ===(q: Term[(A, B)]): Term[Boolean] = Term.===(pair(p))(q)
  private def pair[A, B](p: (Term[A], Term[B])): Term[(A, B)] =
    Term(Tree.Tup(List(p._1.termTree, p._2.termTree)), LeanType.of(Shape.TupleOf(List(p._1.termType, p._2.termType))))
  private[frflow] def pairOf[A, B](a: Term[A], b: Term[B]): Term[(A, B)] = pair((a, b))
  private[frflow] def listOf[A](es: List[Term[A]])(using a: LeanType[A]): Term[List[A]] =
    Term(Tree.ListT(es.map(_.termTree)), LeanType.of(Shape.ListOf(es.headOption.fold(a)(_.termType))))
