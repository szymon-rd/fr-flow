package frflow.proof.lean.lower

import frflow.core.name.{DefName, KbName, ModelName, SymbolName, TypeName}
import frflow.core.ty.{DataType, Ty}
import frflow.proof.lean.ast.*

/** What lowering reads of the FrModel: its name, the open terms each define is over, each model's field of
  * the world and its state's type, what a program's step calls (an operation, by its model's class), each domain
  * type; the programs that may fail, with their error (a run of one is matched on its outcome), whether the world
  * holds faults (a model's operations may fail), and the models' fields of the world, in order.
  */
final case class LowerEnv(kb: KbName, openTerms: DefName => List[LeanName], modelField: ModelName => LeanName,
    operation: SymbolName => LExpr, data: TypeName => Option[DataType], modelState: ModelName => Option[Ty],
    failing: Map[SymbolName, Ty] = Map.empty, faulty: Boolean = false, models: List[LeanName] = Nil)
