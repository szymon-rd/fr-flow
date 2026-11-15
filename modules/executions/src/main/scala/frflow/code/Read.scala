package frflow.code

import frflow.core.code.ReadUnit
import frflow.dsl.compiled.source.ReadCode

/** Code as it was compiled, read from its TASTy as trees. A model whose statements are about an execution of
  * code says which: `history.executing(Read.of(classOf[ThreadHerd], _.endsWith("ThreadHerd.tasty")))`. Nothing of
  * the code is written again or changed; what its trees mean is said in Rocq, once, for any code.
  */
object Read:
  /** The TASTy files of the place `cls` was compiled into (a directory of classes, a jar) whose paths `keep`
    * takes.
    */
  def of(cls: Class[?], keep: String => Boolean = _ => true): List[ReadUnit] = ReadCode.of(cls, keep)
