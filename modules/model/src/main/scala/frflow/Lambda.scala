package frflow

import frflow.program.Lambdas

/** The variables of a lambda over terms, named as the lambda names them, and its body. */
private[frflow] object Lambda:
  def binders(f: AnyRef, types: List[LeanType[?]]): List[Binder] =
    val hints = Lambdas.params(f)
    types.zipWithIndex.map((t, i) => Binder(hints.lift(i).getOrElse("x"), t))
  def body(f: AnyRef, bs: List[Binder]): Term[?] = Building(Fn.call(f, bs.map(_.term[Any])).asInstanceOf[Term[?]])
