package frflow.project.process

/** How a program run by a live interpreter ended: with an exit code, or stopped when it took longer than allowed;
  * its output (standard output and error, in order of lines) kept either way.
  */
enum Exited:
  case Code(exit: Int, output: String)
  case TimedOut(output: String)

  def output: String
  def ok: Boolean = this match
    case Code(0, _) => true
    case _          => false
