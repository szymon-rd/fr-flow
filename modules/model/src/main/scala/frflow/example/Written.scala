package frflow
package example

/** An example written as a test (`FrFlowExamples`): a Definition called on values, and the answer it must give. It is
  * read by `check` and run against the code and against every claim on the Definition; nothing rests on it.
  */
final case class Written(name: String, op: Param[?], inputs: List[Any], answer: Any, suite: String):
  /** As a claim's case: the call allowed, with its answer. */
  def asCase: Example = Example(name, Nil, Nil, inputs, answer, expected = true)

object Written:
  /** `granted(List(…), Booking(…)) is true`, read as a call of `granted` on those values. */
  def of(name: String, expected: Expected, suite: String): Either[String, Written] =
    expected.call.termTree match
      case Tree.Apply(Tree.Ref(op), args) =>
        val values = args.collect { case Tree.Lit(v, _) => v }
        Either.cond(values.size == args.size, Written(name, op, values, expected.answer, suite),
          s"example \"$name\": call ${op.name} on values, not on terms")
      case _ => Left(s"example \"$name\": call a Definition on values (granted(List(…), Booking(…)) is true)")
