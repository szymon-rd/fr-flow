package frflow.proof.lean.lower

import frflow.core.name.{BoundaryName, DefName, KbName, ModelName, TypeName}
import frflow.core.ty.{DataType, Ty}
import frflow.proof.lean.ast.*

/** What lowering reads of the knowledge base: its name, the open terms each define is over, each model's field of
  * the world and its state's type, each boundary's class, each domain type.
  */
final case class LowerEnv(kb: KbName, openTerms: DefName => List[LeanName], modelField: ModelName => LeanName,
    boundaryClass: BoundaryName => LeanName, data: TypeName => Option[DataType], modelState: ModelName => Option[Ty])
