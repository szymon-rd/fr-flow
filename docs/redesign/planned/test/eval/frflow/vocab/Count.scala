package frflow.vocab

import frflow.core.term.{Bound, Ext, Sym}

/** An operation added outside the core: an algebra of its own (LNCS 7470 §2.2, the expression problem's answer: a new
  * operation is a new type class, no central enum edited). An interpreter that knows it says so for its key
  * (`Sym.extension(Count)`); every other runs its meaning in the core (`derived`), so a term using it stays a term
  * over `Sym` and `Term[A]` stays closed. A transformer (`PartialEval`) forwards no extension: it runs the meaning.
  */
trait Count[T[_]]:
  def count[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[BigInt]

object Count extends Ext[Count]:
  /** `s`'s own `count` when it has one, else its meaning: the length of the elements kept. */
  def in[T[_]](s: Sym[T]): Count[T] = s.extension(Count).getOrElse(derived(s))

  def derived[T[_]](s: Sym[T]): Count[T] = new Count[T]:
    def count[A](xs: T[List[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[BigInt] = s.length(s.filter(xs, x)(p))
