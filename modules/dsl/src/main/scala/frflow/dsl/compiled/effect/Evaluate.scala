package frflow.dsl.compiled.effect

import frflow.core.effect.{EType, MethodOf, Program, Pure, Tree as Emitted}
import frflow.core.normal.{NormalMethod, NormalProgram}
import frflow.dsl.lifted.NotRead

/** Stage 2 of the translation (`docs/EFFECT-TREES.md`, 4.1): normalised Scala evaluated into one program per
  * method. What is evaluated without effect is a term in the tree; a local is the value it has; a loop's state
  * is the variables it assigns.
  */
object Evaluate:
  def apply(p: NormalProgram): Program =
    val read = Program(p.sources, p.classes, p.fields, p.methods.map(method), p.outside)
    read.clashes.headOption.foreach(name => throw NotRead(
      s"FrFlow: two things of the code would be written `$name`, so it is not read into trees of effects"))
    read

  private def method(m: NormalMethod): MethodOf =
    val fresh = Fresh()
    val self = fresh("this")
    val params = m.params.map((l, t) => (l, fresh(l.name), t))
    val env = Env(Pure.Local(self), params.map((l, x, _) => l -> Pure.Local(x)).toMap, Set.empty, fresh)
    val tree = Emitted.simplified(EvalStmts.block(m.body, env)((p, _) => Emitted.Give(p)))
    MethodOf(m.name, (self -> EType.Ref) :: params.map((_, x, t) => x -> t), m.gives, tree)
