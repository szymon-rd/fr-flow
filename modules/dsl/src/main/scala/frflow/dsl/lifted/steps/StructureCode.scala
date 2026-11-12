package frflow.dsl.lifted.steps

import frflow.core.name.SymbolName
import frflow.dsl.build.WrittenAt
import frflow.dsl.lifted.FrSpec
import frflow.dsl.vocab.Definition
import scala.annotation.publicInBinary

/** A class that implements a structure, read by FrFlow (`lifted[SpendLimits]`): the record its state is, and
  * each member's code, a function of that record read from the method's body; of a member that changes the
  * structure, also its code among other calls (under `among(member)`). What a structure's word is given
  * (`limits.define(lifted[SpendLimits])`), typed by the class; it is no word to mention in a statement. `held`
  * is each structure the class holds: the word given for it, and how a state of the class gives its state.
  */
final class StructureCode[T] @publicInBinary private[dsl] (called: String, val state: FrSpec[T],
    val code: Map[String, Definition[?]], val held: List[StructureCode.Held])
    extends Definition[T](SymbolName(called), "", None, WrittenAt.none)(using state)

object StructureCode:
  /** A structure a class holds: its word's name, the word that is "what the class holds as it"
    * (`StructureDeclaration.held`), and that word's code, the class's field read.
    */
  final case class Held(part: SymbolName, word: Definition[?], code: Definition[?])

  /** What a member's code among other calls is kept under. */
  def among(member: String): String = s"$member among"
