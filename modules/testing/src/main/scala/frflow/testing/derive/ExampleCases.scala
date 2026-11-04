package frflow.testing.derive

import cats.syntax.all.*
import frflow.core.example.Example
import frflow.core.expr.{Expr, Exprs, Value}
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.testing.Case

/** The cases the examples show of a call: each application of the Definition, in an example's fact, to values of the
  * call's input types, under the example's givens. A node's coverage counts them before its generated cases (what
  * an example shows is reached); whether each holds is the example's own check.
  */
object ExampleCases:
  def of(examples: List[Example], op: SymbolName, inputs: List[Ty]): List[Case] =
    examples.flatMap(e => Exprs.all(e.fact.value).collect {
      case Expr.Apply(Expr.Sym(`op`, _), args, _) if args.size == inputs.size => args
    }.flatMap(args => args.zip(inputs).traverse(literal).map(Case(_, e.givens))))

  /** An argument that is a value of its input's type. */
  private def literal(arg: Expr, input: Ty): Option[Value] = arg match
    case Expr.Lit(v, ty) if ty == input => Some(v)
    case _                              => None
