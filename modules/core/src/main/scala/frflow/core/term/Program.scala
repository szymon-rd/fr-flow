package frflow.core.term

/** A program's run on the models, as Scala holds it: from the world before, its outcome (the error it fails with, or
  * its result) and the world after; Lean's `World → R × World` (`Except E R × World` for a program that can fail). The
  * type of a Definition that is a program is `A => Program[R]`. A model never builds one: a claim states its runs
  * (`Worlds.runs`), and the program itself is a define (`program { … }`).
  */
opaque type Program[R] = World => (Either[Any, R], World)

object Program:
  def of[R](run: World => (Either[Any, R], World)): Program[R] = run
  extension [R](p: Program[R]) def from(before: World): (Either[Any, R], World) = p(before)
