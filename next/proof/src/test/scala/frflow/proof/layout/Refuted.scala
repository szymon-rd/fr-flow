package frflow.proof.layout

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.core.term.{Bound, Stated, Sym}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.Constant
import frflow.proof.terms.TermTable

/** A step that does not hold: `small` (`f n` exactly when `n < 5`) from a part fixing `f` to `n < 3`; refuted at 4. */
object Refuted:
  private val test = Ty.FnOf(List(Lang.big), Ty.Bool)
  private def below(name: String, k: Int) = claim(name)(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("n", Lang.big)(n => l.s.eq(l.call(l.sym[BigInt => Boolean]("f", test), n), l.s.lt(n, l.num(k))))))
  val resolved: Resolved = Resolve(Validate(Kb.of(below("small", 5), below("fixed", 3)).naming(declaration("f", test))
    .linking(partOf("fixed", "small")).elaborated).fold(ps => throw IllegalStateException(ps.toString), identity))
  val table: TermTable = TermTable.of(resolved)
  val found: Refutation = Refutation(Stated([T[_]] => (s: Sym[T]) =>
    s.lam(Bound[BigInt]("n", Lang.big))(n => s.lt(n, Lang(s).num(3)))), test, List(Constant(Value.Num(4), Lang.big)))
  val laid: Laid = Laid(resolved, Map.empty, Nil)
  def modules: List[LeanModule] = laid.modules :+ RefutesModule.of(resolved, table, NodeId("small"), found)
