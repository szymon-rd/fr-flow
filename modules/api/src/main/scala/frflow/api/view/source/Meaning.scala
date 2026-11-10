package frflow.api.view.source

import frflow.core.name.SymbolName

/** How one Definition a node mentions is given its meaning. */
final case class Meaning(definition: SymbolName, by: MeantBy)
