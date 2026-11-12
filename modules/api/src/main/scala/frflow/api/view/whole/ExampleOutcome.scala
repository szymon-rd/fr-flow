package frflow.api.view.whole

/** What an example comes to (owner §18: nothing depends on examples, and their Rocq is a try): it fails (on the code,
  * or Rocq shows the claims contradict it), passes (the code holds it and the claims give it, or Rocq is not asked
  * it), or the code holds it and the claims do not decide it within the budget, which is reported, not failed.
  */
enum ExampleOutcome:
  case Passes, Undecided, Fails
