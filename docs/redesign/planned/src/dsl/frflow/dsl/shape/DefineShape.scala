package frflow.dsl.shape

import frflow.dsl.term.{LeanType, Term}

/** The shape of a define of type `F`: a lambda over its inputs, their types and the result's. One instance per arity.
  */
trait DefineShape[F]:
  type Lam <: AnyRef
  def types: List[LeanType[?]]
  def call(f: Lam, args: List[Term[Any]]): Term[?]

object DefineShape:
  given one[A, R](using a: LeanType[A]): DefineShape[A => R] with
    type Lam = Term[A] => Term[R]
    val types: List[LeanType[?]] = List(a)
    def call(f: Lam, args: List[Term[Any]]): Term[?] = args match
      case List(x) => f(x.asInstanceOf[Term[A]]) // the binder was made of exactly this type by `Elab.lambda`
      case _       => throw IllegalArgumentException("FrFlow bug: a define of one input called with others")
  // … for 0 to 6 inputs.
