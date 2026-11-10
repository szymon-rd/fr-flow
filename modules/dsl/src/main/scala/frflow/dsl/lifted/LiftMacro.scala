package frflow.dsl.lifted

import frflow.dsl.term.Term
import scala.quoted.*

/** `lifted`'s reading of its function, at compile time: the function's body as a function of its inputs' terms
  * (`Reader`), one entry per number of inputs.
  */
object LiftMacro:
  inline def read1[A, R](inline f: A => R): Term[A] => Term[R] = ${ one[A, R]('f) }
  inline def read2[A, B, R](inline f: (A, B) => R): (Term[A], Term[B]) => Term[R] = ${ two[A, B, R]('f) }
  inline def read3[A, B, C, R](inline f: (A, B, C) => R): (Term[A], Term[B], Term[C]) => Term[R] =
    ${ three[A, B, C, R]('f) }
  inline def read4[A, B, C, D, R](inline f: (A, B, C, D) => R): (Term[A], Term[B], Term[C], Term[D]) => Term[R] =
    ${ four[A, B, C, D, R]('f) }

  def one[A: Type, R: Type](f: Expr[A => R])(using q: Quotes): Expr[Term[A] => Term[R]] = Reader(q).lambda1(f)
  def two[A: Type, B: Type, R: Type](f: Expr[(A, B) => R])(using q: Quotes): Expr[(Term[A], Term[B]) => Term[R]] =
    Reader(q).lambda2(f)
  def three[A: Type, B: Type, C: Type, R: Type](f: Expr[(A, B, C) => R])(using q: Quotes)
      : Expr[(Term[A], Term[B], Term[C]) => Term[R]] = Reader(q).lambda3(f)
  def four[A: Type, B: Type, C: Type, D: Type, R: Type](f: Expr[(A, B, C, D) => R])(using q: Quotes)
      : Expr[(Term[A], Term[B], Term[C], Term[D]) => Term[R]] = Reader(q).lambda4(f)
