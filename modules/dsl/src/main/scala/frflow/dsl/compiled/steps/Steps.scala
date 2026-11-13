package frflow.dsl.compiled.steps

import frflow.dsl.compiled.Compiler
import frflow.dsl.term.{Lift, TermSyntax}
import frflow.dsl.term.Term as DTerm

/** Scala that changes a port, compiled into state passing, as Aeneas reads Rust's `&mut`: the port's variable
  * stands for its state; a call of an `update` method is the state its body leaves; what follows a change reads
  * the new state; a conditional that changes the state gives the state either branch leaves. What changes nothing
  * is read by the compiler of expressions (`c`). Read among other calls, each call of a held structure is a step:
  * before it the others may have left another state, and what it did is kept in the traces. Sound because the
  * port is the code's alone, which Scala's separation checking checks where the code is compiled.
  */
private[steps] final class Steps(val c: Compiler) extends StepPorts, StepCalls, StepWalk:
  import c.q.reflect.*
  import c.given

  /** `t` run from the state `key` is bound to: its value and where the reading is after it, given to the rest. */
  def run(t: Term, as: TypeRepr, key: Symbol)(rest: Rest)(using walk: Walk): DTerm[Any] = c.bare(t) match
    case pure if quiet(pure)                             => rest(c.read(pure, as)(using walk.env), walk)
    case Block(Nil, e)                                   => run(e, as, key)(rest)
    case Block((v @ ValDef(_, tpt, Some(rhs))) :: ss, e) => run(rhs, tpt.tpe.widen, key)((x, after) =>
      named(v.name, x)(y => run(Block(ss, e), as, key)(rest)(using after.bound(v.symbol, y)))(using after))
    case Block((s: Term) :: ss, e)                       =>
      run(s, s.tpe.widen, key)((_, after) => run(Block(ss, e), as, key)(rest)(using after))
    case Assign(to, value) if c.partOf(portOf(key).typeRef, to.symbol, t).nonEmpty => assigned(value, to, key)(rest)
    case branch @ If(cond, _, _) if quiet(cond)          => either(branch, as, key)(rest)
    case call if storeCall(call)                         => step(call, as)(rest)
    case call if holderCall(call)                        => called(call)(rest)
    case other                                           => c.refuse("a use of a port here: a port is used in a " +
      "statement of its own (`val x = port.call(…)`), an `if`'s branch, or an `update` method's body", other)

  /** The state a `var`'s assignment leaves: the value assigned, named for what follows. */
  private def assigned(value: Term, to: Term, key: Symbol)(rest: Rest)(using Walk): DTerm[Any] =
    run(value, to.tpe.widen, key)((x, after) => named(to.symbol.name, x)(y =>
      putAt(Place(key, c.partOf(portOf(key).typeRef, to.symbol, to).flatten.toList), y)(
        rest(c.any(Lift.constant[Unit](())), _))(using after))(using after))

  /** A conditional that changes the state: its value with what either branch leaves, named for what follows. */
  private def either(branch: If, as: TypeRepr, key: Symbol)(rest: Rest)(using walk: Walk): DTerm[Any] =
    val joined = walk.copy(out = packedType(c.spec(as, branch)))
    def side(t: Term): DTerm[Any] = run(t, as, key)((x, w) => packed(x)(using w))(using joined)
    val steps = walk.step + count(branch.thenp).max(count(branch.elsep))
    val cond = c.asTruth(c.read(branch.cond, TypeRepr.of[Boolean])(using walk.env), branch.cond)
    c.bind(TermSyntax.when(cond)(side(branch.thenp)).otherwise(side(branch.elsep)), "after") { p =>
      val (v, carried) = unpacked(p)
      rest(v, derived(key)(using walk.copy(env = walk.env ++ carried, step = steps)))
    }(using walk.out)
