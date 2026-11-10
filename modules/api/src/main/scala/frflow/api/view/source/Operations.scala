package frflow.api.view.source

import frflow.core.name.ModelName

/** A model's operations' Scala, tested against the model, as written. */
final case class Operations(model: ModelName, scala: String)
