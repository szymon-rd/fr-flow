package frflow

val stock = Boundary[Stock]("stock", "the books in stock")

/** Restocks each of the deliveries, then says how many there are. */
def restock(ds: Term[List[BigInt]]): Flow[BigInt] =
  for
    before <- stock.count
    _ <- ds.traverse_(d => stock.add(d))
    after <- stock.count
  yield after - before

/** Restocks twice the delivery, naming the doubled amount once. */
def restockTwice(d: Term[BigInt]): Flow[BigInt] =
  for
    before <- stock.count
    twice = d + d
    _ <- stock.add(twice)
    _ <- stock.add(twice)
    after <- stock.count
  yield twice
