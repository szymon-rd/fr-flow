package frflow.api.view.vocab

/** The words a model is written in, as a reader looks them up: its Declarations and Definitions, its defines and
  * its domain types.
  */
final case class Vocab(symbols: List[Word], defines: List[Defined], types: List[DomainType])
