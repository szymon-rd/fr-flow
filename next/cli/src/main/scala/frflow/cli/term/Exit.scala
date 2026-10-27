package frflow.cli.term

import cats.effect.ExitCode

/** The CLI's exit codes: 0 fine; 1 something is not accepted or proven, or a decision was refused; 2 a usage error
  * (an unknown node among them); 3 no Lean.
  */
object Exit:
  val Fine: ExitCode = ExitCode.Success
  val Refused: ExitCode = ExitCode(1)
  val Usage: ExitCode = ExitCode(2)
  val NoLean: ExitCode = ExitCode(3)

  def of(ok: Boolean): ExitCode = if ok then Fine else Refused
