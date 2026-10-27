package frflow.fixtures

import frflow.*

final case class Book(title: String, pages: Int)
object Book extends Data[Book]

/** A box of books: a record holding values of a type with an `always`. */
final case class Box(label: String, books: List[Book])
object Box extends Data[Box]

/** A case class with no companion written: built from terms by its name all the same. */
final case class Plain(a: String, n: BigInt)
