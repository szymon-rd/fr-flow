package frflow.dsl.compiled.steps

import frflow.dsl.compiled.Inspect
import frflow.dsl.lifted.steps.{StructureCode, StructureType}
import frflow.dsl.structure.StructureDeclaration
import frflow.dsl.term.{Lift, Term}
import scala.reflect.ClassTag

/** A class given as a structure's Definition, and an object of it as a state, both read from the TASTy the
  * compiler wrote for the class: no macro where they are written, and nothing the compiler must keep.
  */
object ClassSyntax:
  /** `lifted[RecordedLimits]`: a class that implements a structure, compiled member by member from its TASTy as
    * the model is built: what the structure's word is defined by (`limits.define(lifted[RecordedLimits])`), each
    * member checked against every claim on it. Scala the compiler does not read is a `NotRead` there, with its
    * file and line.
    */
  def lifted[C](using c: ClassTag[C]): StructureCode[C] = compiled[C](c.runtimeClass, Nil)

  /** The same of a class that holds structures, given the word of each in the order its constructor takes them
    * (`lifted[StreamPaymentHandler](limits, ledger, offsets)`).
    */
  def lifted[C](words: StructureDeclaration[?]*)(using c: ClassTag[C]): StructureCode[C] =
    compiled[C](c.runtimeClass, words.toList)

  private def compiled[C](cls: Class[?], words: List[StructureDeclaration[?]]): StructureCode[C] =
    Inspect(cls)(q => ClassCode.of(q, cls.getName.replace('$', '.'), words, cls.getClassLoader))
      .asInstanceOf[StructureCode[C]] // typed by the class it was asked of

  extension [T](structure: StructureDeclaration[T])
    /** The structure as an object of a class that implements it has it, for an example
      * (`limits.holding(RecordedLimits(BigInt(100), Nil))`): the object's fields' values, in the record its
      * class's state is.
      */
    def holding(made: T): Term[structure.Is] =
      val state = Inspect(made.getClass)(q => ClassCode.state(q, made))
      Lift.constant[Any](StructureType.held(state, made))(using state).asInstanceOf[Term[structure.Is]]
