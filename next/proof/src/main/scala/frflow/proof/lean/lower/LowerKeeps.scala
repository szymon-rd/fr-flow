package frflow.proof.lean.lower

import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Form, Written}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed
import frflow.proof.obligation.Prop
import frflow.proof.terms.TermTable

/** That every run of a program keeps what always holds, or every result of a maker meets it, as the claims module
  * declares it in the `always`'s namespace, over what it mentions: `def keeps_book (book : Booking → World → (Prop ×
  * World)) : Prop := ∀ …`, `def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop := ∀ …`. The
  * code is asked it (`cover_<op>`, `Prop.Keeps`; `made_<maker>`, `Prop.Makes`).
  */
final class LowerKeeps(env: LowerEnv, table: TermTable, naming: Naming):
  def apply(k: Prop.Keeps): Decl = declared(k.always, s"keeps_${k.op.value}", k.formula)
  def makes(m: Prop.Makes): Decl = declared(m.always, s"makes_${m.maker.value}", m.formula)

  private def declared(always: NodeId, name: String, formula: Written[Expr]): Decl =
    val params = LowerProp.opens(formula).symbols.map(s =>
      LBinder.Explicit(Names.ident(s.value), LowerType.binder(typeIn(formula, s))))
    val body = formula.form match
      case Form.Term(t)  => Printed.formula(env, naming)(t.run)
      case Form.Steps(_) => throw IllegalStateException("FrFlow bug: a program's steps as a formula")
    Decl.Namespace(Names.path(env.kb.value, always.value),
      List(Decl.Def(List(Attr.FrflowDefs), Names.builtin(name), params, Atoms.name("Prop"), body)))

  /** A symbol's type as the formula holds it (a store operation is no symbol of the vocabulary), else the table's. */
  private def typeIn(f: Written[Expr], s: SymbolName): Ty =
    Exprs.all(f.value).collectFirst { case Expr.Sym(`s`, ty) => ty }.getOrElse(table.typeOf(s))
