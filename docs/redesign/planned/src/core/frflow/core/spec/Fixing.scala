package frflow.core.spec

import frflow.core.expr.{Expr, Lambda}
import frflow.core.name.{SymbolName, TypeName}
import frflow.core.ty.Ty

/** What a definition fixes: an opaque type as a type (`User := of[UserId]`), or a symbol as a function of the domain
  * (`authorized := (u, p) => …`; a value is a lambda of no parameters).
  */
enum Fixing:
  case TypeAs(sort: TypeName, as: Ty)
  case TermAs(symbol: SymbolName, as: Written[Lambda])

  def exprs: List[Expr] = this match
    case TypeAs(_, _)  => Nil
    case TermAs(_, as) => List(as.value.body)
