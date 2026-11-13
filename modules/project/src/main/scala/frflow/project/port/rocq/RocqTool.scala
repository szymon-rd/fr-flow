package frflow.project.port.rocq

import frflow.project.process.Command

/** Rocq as a build runs it: the program, how long one compile may take, and the memory one may use, in megabytes. A
  * proof search that outgrows it is stopped by Rocq, and reported of its lemma, before the machine stops it.
  */
final case class RocqTool(command: Command, memoryMb: Int):
  /** `rocq` with these arguments under the memory limit, where the shell sets one: the command to run, and its
    * arguments.
    */
  def limited(args: List[String]): (Command, List[String]) =
    val script = s"ulimit -v ${memoryMb.toLong * 1024} 2>/dev/null; exec \"$$0\" \"$$@\""
    (command.copy(program = "sh"), List("-c", script, command.program) ++ args)

object RocqTool:
  /** The memory a compile may use when the environment names none. */
  val Memory: Int = 4000
