package frflow.core.expr

import frflow.core.ty.Ty

/** A function of the IR: its parameters, its body and the body's type. */
final case class Lambda(params: List[Binder], body: Expr, result: Ty):
  def arity: Int = params.size
