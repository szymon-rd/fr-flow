package frflow

object StockModel extends Stock, StateModel[BigInt]:
  def count = state.get
  def add(n: Term[BigInt]) = state.update(c => c + n)
