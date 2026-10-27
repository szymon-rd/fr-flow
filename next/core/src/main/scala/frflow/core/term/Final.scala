package frflow.core.term

/** A term in final form: what it is for every interpreter (LNCS 7470 §2.1, the final embedding; closed over `Sym`). */
type Final[A] = [T[_]] => Sym[T] => T[A]
