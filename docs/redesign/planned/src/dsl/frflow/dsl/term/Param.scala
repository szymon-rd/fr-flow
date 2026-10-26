package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.expr.Expr
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType}
import frflow.dsl.build.{Declarations, Failure, Fault, Fresh}

/** A domain term, open until a definition fixes it: as a term, the symbol; in plain code, its value in force. */
final class Param[A](val name: SymbolName, val means: String)(using t: LeanType[A])
    extends Term[A](Expr.Sym(name, t.ty), Notes.of(t.declares |+| Param.declares(name, means, t.ty))):
  /** Its value where code runs. Read while building a term, it would become a constant of the Lean and the Scala. */
  def value: A =
    if Fresh.active then throw Failure(Fault.ValueReadWhileBuilding(name))
    Values.read(name).getOrElse(throw IllegalStateException(s"${name.value} is not bound where this code runs"))
      .asInstanceOf[A] // bound by its own `bind`, typed `A`

object Param:
  def apply[A: LeanType](name: String, means: String): Param[A] = new Param[A](SymbolName(name), means)
  private def declares(name: SymbolName, means: String, ty: Ty): Declarations =
    Declarations.symbol(Symbol(name, means, SymbolType.Typed(ty)))
