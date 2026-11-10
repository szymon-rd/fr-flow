package frflow.dsl.lifted

import frflow.dsl.build.AsWritten
import frflow.dsl.term.Term

/** A type's contract: the rule every value of the type meets, as a function of the value's term, with the text it
  * was written as. Written in plain Scala (`FrSpec.where`), it is read into the term and kept as the Scala it is,
  * which checks a value where the code runs (`native`); written with the DSL (`FrSpec.whereStated`: a rule plain
  * Scala cannot say, over every value of a type), it is the term alone.
  */
enum Contract[A]:
  case Plain(rule: Term[A] => Term[Boolean], native: A => Boolean, written: AsWritten)
  case Stated(rule: Term[A] => Term[Boolean], written: AsWritten)

  def rule: Term[A] => Term[Boolean]
  def written: AsWritten
