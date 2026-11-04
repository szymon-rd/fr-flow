package frflow.proof.layout

import frflow.core.term.Stated
import frflow.core.ty.Ty
import frflow.proof.obligation.Constant

/** What refutes a step: an answer the node's one part allows (a term of the type of the Definition its call is
  * about) and the case on which the node's claim fails with it.
  */
final case class Refutation(answer: Stated[?], ty: Ty, inputs: List[Constant])
