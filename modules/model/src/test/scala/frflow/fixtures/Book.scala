package frflow.fixtures

import frflow.*

final case class Book(title: String, pages: Int)
object Book extends Data[Book]
