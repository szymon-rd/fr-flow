package sharing

/** Sharing's examples in Lean, against today's: a difference judged, as `Judged`'s of the nodes are. */
object JudgedExamples:
  /** Today's 119/119 (reference/sharing/check.txt): each of its 99 operation examples decided by `frflow_eval`
    * evaluating its contract's post on the closed values it gives, and run through the code in Lean (`evalImpl_<i>`),
    * beside 20 examples of flows. Now each of the 99 is `example_<set>_<i>`: the fact proven from the claims for
    * every meaning of what it mentions (`ExampleGoals`), a stronger statement tried within 20,000 heartbeats, so
    * Lean's automation decides fewer; and its opposite, shown of none. In Scala nothing is lost: all 99 hold on the
    * code (`SeededSuite`), and today's 20 flow examples run in production's interpreter, 99 + 20 = today's 119.
    */
  val differs: (String, String) = "examples in Lean: today's 119/119, now 10/99 given by the claims, 89 not " +
    "decided, none contradicted" -> ("the rebuilt obligation proves each example from the claims, for every " +
      "meaning, where today's evaluated closed values")

  /** The examples the claims give, by class and place (`example_<set>_<i>` shown). */
  val shown: Set[(String, Int)] =
    (0 to 3).map("ChaseExamples" -> _).toSet ++ (0 to 2).map("ReminderDueExamples" -> _) ++
      (0 to 2).map("WarnExamples" -> _)
