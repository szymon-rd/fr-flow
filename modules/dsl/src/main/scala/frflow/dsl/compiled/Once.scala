package frflow.dsl.compiled

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.interpret.Substituted
import frflow.core.term.language.Sym
import frflow.dsl.term.RocqType
import frflow.dsl.term.Term as DTerm

/** A binder's body, compiled once, as the class is read: the body over variables of its own, each of which
  * whoever binds it then gives its value (`Substituted`). The term language takes a body as a function of its
  * variable's term and calls it each time the term is interpreted; a body that read the TASTy then would read it
  * long after the class was compiled. So the TASTy is read once, and Scala that is not read is refused where the
  * class is lifted.
  */
private[compiled] final class Once private (next: () => Int):
  def apply(vars: List[(String, RocqType[Any])])(body: List[DTerm[Any]] => DTerm[Any])
      : List[DTerm[Any]] => DTerm[Any] =
    val own = vars.map((hint, of) => Binder(VarId.step(next()), s"once$$$hint", of.ty))
    val compiled = body(own.zip(vars).map((x, v) => DTerm.free[Any](x)(using v._2)))
    given_ => DTerm([T[_]] => (s: Sym[T]) =>
      compiled.run(Substituted(s, own.zip(given_.map(_.run(s).asInstanceOf[T[Any]])).toMap)))(using
      compiled.rocqType)

private[compiled] object Once:
  /** A supply of variables for one class's compiling: each its own, so a body inside another's never takes the
    * other's variable for its own. The count is this supply's alone, and one class is compiled by one thread.
    */
  def apply(): Once =
    var made = 0
    new Once(() => { made += 1; made })
