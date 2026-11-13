package frflow.proof.prover.lower

import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{ProverNames, NodeId, SymbolName}
import frflow.core.spec.{Form, Written}
import frflow.core.ty.Ty
import frflow.proof.prover.ast.*
import frflow.proof.prover.term.Printed
import frflow.proof.obligation.Prop
import frflow.proof.terms.{OpenTerms, TermTable}

/** That every result of a maker meets what always holds, as the claims module declares it in the `always`'s
  * namespace, over what it mentions: `def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  * ∀ …`. The code is asked it (`made_<maker>`, `Prop.Makes`).
  */
final class LowerKeeps(env: LowerEnv, table: TermTable, naming: Naming):
  def makes(m: Prop.Makes): Decl = declared(m.always, ProverNames.makes(m.maker.value), m.formula)

  private def declared(always: NodeId, name: String, formula: Written[Expr]): Decl =
    val params = LowerKeeps.opens(formula, table).symbols.map(s =>
      LBinder.Explicit(Names.ident(s.value), LowerType.binder(typeIn(formula, s))))
    val body = formula.form match
      case Form.Term(t) => Printed.formula(env, naming)(t.run)
    Decl.Namespace(Names.path(env.kb.value, always.value),
      List(Decl.Def(List(Attr.FrflowDefs), Names.builtin(name), params, Atoms.name("Prop"), body)))

  /** A symbol's type as the formula holds it, else the table's. */
  private def typeIn(f: Written[Expr], s: SymbolName): Ty =
    Exprs.all(f.value).collectFirst { case Expr.Sym(`s`, ty) => ty }.getOrElse(table.typeOf(s))

object LowerKeeps:
  /** What a formula is over: the symbols it mentions, in order, and those the defines it calls are over.
    */
  def opens(f: Written[Expr], table: TermTable): OpenTerms =
    val said = Exprs.mentions(f.value)
    OpenTerms(Nil, (said.symbols ++ said.defines.flatMap(table.defines.getOrElse(_, OpenTerms.empty).symbols)).distinct)
