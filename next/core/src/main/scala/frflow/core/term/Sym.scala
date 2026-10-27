package frflow.core.term

import frflow.core.term.algebra.*

/** FrFlow's term language: every algebra an interpreter of a model's terms implements (LNCS 7470 §3.2, `Symantics`;
  * Carette, Kiselyov and Shan, JFP 2009, §2). The closed `dsl.term.Term[A]` is a term over this bundle. An algebra
  * added outside the core is found by its key (`extension`): an interpreter that implements it says so; any other
  * gives `None`, and the term runs the operation's meaning in this bundle.
  */
trait Sym[T[_]] extends Logic[T], Equality[T], Arith[T], Constants[T], Lists[T], Options[T], Eithers[T],
    Quantifiers[T], Records[T], Sums[T], Functions[T], Named[T], Variables[T], Worlds[T], Annotations[T]:
  def extension[E[_[_]]](key: Ext[E]): Option[E[T]] = None
