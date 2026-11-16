package frflow.project.port.rocq

import frflow.project.process.Command

/** Rocq as a build runs it: the program, how long one compile may take, the memory one may use, in megabytes, and
  * how many compiles may run at once (`jobs`). A proof search that outgrows the memory is stopped by Rocq, and
  * reported of its lemma, before the machine stops it.
  */
final case class RocqTool(command: Command, memoryMb: Int, jobs: Int):
  /** `rocq` with these arguments under the memory limit, where the shell sets one: the command to run, and its
    * arguments.
    */
  def limited(args: List[String]): (Command, List[String]) =
    val script = s"ulimit -v ${memoryMb.toLong * 1024} 2>/dev/null; exec \"$$0\" \"$$@\""
    (command.copy(program = "sh"), List("-c", script, command.program) ++ args)

object RocqTool:
  /** The memory a compile may use when the environment names none. */
  val Memory: Int = 4000

  /** The compiles at once when the environment names no number: one fewer than the machine's processors, which
    * leaves FrFlow its own, and keeps what a try may take in seconds about what it takes alone.
    */
  def jobs: Int = (Runtime.getRuntime.availableProcessors - 1).max(1)
