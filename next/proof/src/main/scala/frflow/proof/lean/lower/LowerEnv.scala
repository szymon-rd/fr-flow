package frflow.proof.lean.lower

import frflow.core.name.{BoundaryName, DefName, KbName, ModelName, SymbolName, TypeName}
import frflow.core.ty.{DataType, Ty}
import frflow.proof.lean.ast.*

/** What lowering reads of the knowledge base: its name, the open terms each define is over, each model's field of
  * the world and its state's type, each boundary's class, each domain type; the programs that may fail, with their
  * error (a run of one is matched on its outcome), whether the world holds faults (a boundary may fail), and the
  * models' fields of the world, in order.
  */
final case class LowerEnv(kb: KbName, openTerms: DefName => List[LeanName], modelField: ModelName => LeanName,
    boundaryClass: BoundaryName => LeanName, data: TypeName => Option[DataType], modelState: ModelName => Option[Ty],
    failing: Map[SymbolName, Ty] = Map.empty, faulty: Boolean = false, models: List[LeanName] = Nil)
