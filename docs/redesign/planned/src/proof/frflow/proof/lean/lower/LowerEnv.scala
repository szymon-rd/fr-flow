package frflow.proof.lean.lower

import frflow.core.name.{BoundaryName, DefName, KbName, ModelName, TypeName}
import frflow.core.ty.DataType
import frflow.proof.lean.ast.*

/** What lowering reads of the FrModel. */
final case class LowerEnv(kb: KbName, openTerms: DefName => List[LeanName], modelField: ModelName => LeanName,
    boundaryClass: BoundaryName => LeanName, data: TypeName => Option[DataType])
