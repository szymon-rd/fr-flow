package frflow.fixtures

import frflow.*

enum Shelf:
  case Top, Bottom
  case Box(label: String)
object Shelf extends Data[Shelf]
