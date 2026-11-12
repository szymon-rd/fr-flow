package frflow.project.process

/** What of a program's output a run keeps: its standard error's lines among its standard output's; its standard
  * output alone, as written (git's, which is data); or its standard output when it exits with 0 and its standard
  * error when it does not (Rocq's: what it printed, or the error it stopped at).
  */
enum Output:
  case Merged, Standard, ByExit
