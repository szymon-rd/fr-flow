package frflow.core.term

/** The key of an algebra added outside the core, `E` (`object Count extends Ext[Count]`): an interpreter that
  * implements `E` returns itself for it from `Sym.extension`, matched on the key's type, with no cast.
  */
trait Ext[E[_[_]]]
