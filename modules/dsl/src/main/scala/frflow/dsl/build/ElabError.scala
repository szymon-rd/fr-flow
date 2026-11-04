package frflow.dsl.build

/** What keeps a model from elaborating, and where. */
final case class ElabError(at: Site, fault: Fault)
