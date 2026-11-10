package frflow.api.view.source

/** What a node is written in: how each Definition it mentions is given its meaning, the operations' Scala of the
  * model its assumption is about, the project's files its code is in, its Lean as FrFlow generates it (its own
  * modules, then those of the defines it rests on), and the developer's proof of it, if there is one.
  */
final case class Sources(meanings: List[Meaning], operations: List[Operations], files: List[SourceFile],
    generated: List[LeanText], proof: Option[LeanText])
