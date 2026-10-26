package frflow.proof.terms

import frflow.core.ty.Ty

/** What a term is in force as, where a statement applies it: an opaque type as a type, a symbol as its defining
  * term applied to that term's own open terms.
  */
enum FixedAs:
  case Type(ty: Ty)
  case Term(over: OpenTerms)
