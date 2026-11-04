package sharing

import frflow.*
import sharing.examples.*

/** Today's examples of sharing's operations, each a test beside the model (owner §18): one class per contract they
  * were written on, in today's order. Today's examples of the three programs, on the models' worlds, are runs in
  * the port's suites.
  */
object Examples:
  val written: List[FrFlowExamples] = List(AccessExamples(), CanViewExamples(), CanEditExamples(), ShareExamples(),
    UnshareExamples(), MoveExamples(), InviteExamples(), AcceptExamples(), WithdrawExamples(), TrashExamples(),
    RestoreExamples(), AskExamples(), ApproveExamples(), DeclineExamples(), ChaseExamples(), TransferExamples(),
    RecordExamples(), ForgetExamples(), AnnounceExamples(), WarnExamples(), TidyExamples(), InForceExamples(),
    IsOpenExamples(), GoneExamples(), PendingExamples(), ReminderDueExamples())
