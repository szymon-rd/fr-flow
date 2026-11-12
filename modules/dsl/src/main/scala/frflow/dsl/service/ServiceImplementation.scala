package frflow.dsl.service

import frflow.core.name.SymbolName
import frflow.dsl.build.WrittenAt
import frflow.dsl.lifted.FrSpec
import frflow.dsl.vocab.Definition
import scala.annotation.publicInBinary

/** A class that implements a service, read by FrFlow (`lifted(SpendLimits(…))`): the record its state is, and
  * each member's code, a function of that record read from the method's body. What `implementProven` gives a
  * service's Definition; it is no Definition to mention in a statement.
  */
final class ServiceImplementation[T] @publicInBinary private[dsl] (called: String, val state: FrSpec[T],
    val code: Map[String, Definition[?]]) extends Definition[T](SymbolName(called), "", None, WrittenAt.none)(
      using state)
