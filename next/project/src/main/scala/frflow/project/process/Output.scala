package frflow.project.process

/** What of a program's output a run keeps: its standard error's lines among its standard output's (Lean's messages
  * come on both), or its standard output alone, as written (git's, which is data).
  */
enum Output:
  case Merged, Standard
