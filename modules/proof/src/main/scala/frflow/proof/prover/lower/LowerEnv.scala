package frflow.proof.prover.lower

import frflow.core.name.{DefName, KbName, TypeName}
import frflow.core.ty.DataType
import frflow.proof.prover.ast.*

/** What lowering reads of the FrModel: its name, the open terms each define is over, each domain type, and the
  * defines a rule calls that are lowered twice (`layout.RuleSide`).
  */
final case class LowerEnv(kb: KbName, openTerms: DefName => List[ProverName], data: TypeName => Option[DataType],
    twice: Set[DefName] = Set.empty, ruleSide: Boolean = false):
  /** The `def` a call of `d` names: of a define a rule calls, lowered twice (`layout.RuleSide`), the guarded one but
    * where a rule's side is printed (`ruleSide`: a rule, and what it calls).
    */
  def calls(d: DefName): DefName = if twice(d) && !ruleSide then LowerEnv.guarded(d) else d

object LowerEnv:
  /** The second `def` of a define a rule calls, its `forall`s guarded, which statements call. */
  def guarded(d: DefName): DefName = DefName(s"${d.value}_guarded")
