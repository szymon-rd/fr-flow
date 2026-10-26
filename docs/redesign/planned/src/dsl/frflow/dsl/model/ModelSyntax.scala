package frflow.dsl.model

import frflow.core.name.ModelName
import frflow.dsl.build.Source
import frflow.dsl.flow.{Boundary, Recorded}
import frflow.dsl.term.{LeanType, Term}

/** A boundary's model as a model writes it: `store.model("every booking …")(Stored(_))`. */
object ModelSyntax:
  extension [B[_[_], _[_]]](boundary: Boundary[B])
    /** Its model, named as its val: a state of `S` and the developer's instance of the trait over it. */
    inline def model[S](means: String)(instance: Model[Recorded, S] => B[Recorded, Term])(
        using LeanType[S]): StoreModel[B, S] =
      StoreModel(new ModelState[S](ModelName(Source.valName), means), boundary, instance)
