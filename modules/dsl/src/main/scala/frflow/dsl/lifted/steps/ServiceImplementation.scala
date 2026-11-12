package frflow.dsl.lifted.steps

import frflow.core.name.SymbolName
import frflow.dsl.build.WrittenAt
import frflow.dsl.lifted.FrSpec
import frflow.dsl.vocab.Definition
import scala.annotation.publicInBinary

/** A class that implements a service, read by FrFlow (`lifted(SpendLimits(…))`): the record its state is, and
  * each member's code, a function of that record read from the method's body; of a member that changes the
  * service, also its code among other calls (under `among(member)`). What a service's word is given
  * (`limits.define(lifted(SpendLimits(…)))`), typed by the class; it is no word to mention in a statement.
  */
final class ServiceImplementation[T] @publicInBinary private[dsl] (called: String, val state: FrSpec[T],
    val code: Map[String, Definition[?]]) extends Definition[T](SymbolName(called), "", None, WrittenAt.none)(
      using state)

object ServiceImplementation:
  /** What a member's code among other calls is kept under. */
  def among(member: String): String = s"$member among"
