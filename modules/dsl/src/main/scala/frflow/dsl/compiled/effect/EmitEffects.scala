package frflow.dsl.compiled.effect

import frflow.core.effect.Program
import frflow.dsl.compiled.normal.Normalise

/** Compiled Scala read as trees of effects (`docs/EFFECT-TREES.md`), in two stages: the classes of the TASTy
  * files a class was compiled beside are read into normalised Scala (`Normalise`), which is then evaluated into
  * one program per method (`Evaluate`). Scala that is not read is refused with its place (`NotRead`).
  */
object EmitEffects:
  /** The program of the files, of the directory `cls` was compiled into, whose paths `keep` takes. */
  def apply(cls: Class[?], keep: String => Boolean): Program = Evaluate(Normalise(cls, keep))
