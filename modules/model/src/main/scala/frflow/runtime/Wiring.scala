package frflow
package runtime

import frflow.protocol.{NodeKind, RunCheck}

// The run-time path: the user's production code calls `service`'s plain function of the operation's inputs, and the
// predicates it checks read parameters as `param.value` deep inside the user's own code. That path has no
// effect type, so:
// - The values in force are a ThreadLocal (`Bindings`): there is no argument to pass them through.
// - A broken contract or assumption is reported (`Violation`, to the FrModel's reporter: a log line by
//   default), then thrown as `ContractViolation`, so that a result that breaks it is never returned (fail closed);
//   a wiring mistake (no implementation, an unbound parameter) is an `IllegalStateException` when the service is
//   wired, not on the first call.
// - Which calls are checked is the contract's `RunCheck`: every call for code Lean does not prove, none for
//   code it proves, or a sample, as the developer decides.
// - A running service remembers, in an atomic reference, what each assumption was last found to hold of; a call
//   reads each parameter once, through a `Cell`.

/** Wiring a FrModel's code into a running system (see `FrModel.service`). */
private[frflow] object Wiring:
  def service[F](kb: FrModel, contract: Node[F], bindings: Seq[Binding]): F =
    val i = kb.implementation(contract).getOrElse(throw IllegalStateException(s"no implementation of ${contract.id}"))
    val bound = bindings.map(_.param.name).toSet
    val defined = kb.definitionBindings.filterNot(b => bound(b.param.name))
    val calls = Wiring.calls(kb, bindings).filterNot(b => bound(b.param.name) || contract.op.exists(_ eq b.param))
    // Fail when wired, not on the first call: every parameter the contract or its examples read must be bound
    // (a contract that starts reading a new parameter breaks old wiring here).
    val auto = (defined ++ calls).map(_.param.name).toSet
    val needed = (contract.post.toList.flatMap(kb.reads) ++ contract.cases.flatMap(_.bindings.map(_.param.name))).distinct
      .filterNot(p => auto(p) || contract.op.exists(_.name == p))
    val missing = needed.filterNot(bound)
    if missing.nonEmpty then throw IllegalStateException(s"${contract.id}: bind ${missing.mkString(", ")} (the contract reads them)")
    val all = bindings ++ defined ++ calls
    val assumes = kb.runtimeAssumptions.filter(_.reads.subsetOf(bound))
    Bindings.within(all)(assumes.find(!_.holds())).foreach { x =>
      val v = Violation(contract.id, s"the assumption ${x.what}", Nil, None)
      kb.onViolation(v)
      throw ContractViolation(v)
    }
    // A Definition's code runs as it is: proofs and tests check it before production.
    val runTime = kb.runTime(contract).map(_.check)
      .getOrElse(if i.definition.isDefined then RunCheck.Never else RunCheck.EveryCall)
    // The code is built on each call, under the values in force then.
    val code = Fn.of(contract.op.map(Node.arity).getOrElse(0))(ins => Fn.call(i.factory(), ins)).asInstanceOf[F]
    contract.enforce(code, assumes, runTime, kb.onViolation)(all*)

  /** Each operation some contract's code implements, bound to its service (made when first called); a Definition's
    * code, to that code itself.
    */
  def calls(kb: FrModel, bindings: Seq[Binding]): List[Binding] =
    opBindings(kb) { (c, i) =>
      if i.definition.isDefined then () => i.factory()
      else
        lazy val s: AnyRef = service(kb, c.asInstanceOf[Node[AnyRef]], bindings)
        val g = Fn.of(c.op.map(Node.arity).getOrElse(0))(ins => Fn.call(s, ins))
        () => g
    }

  def definitionBindings(kb: FrModel): List[Binding] =
    kb.provisional.toList.sortBy(_._1).flatMap((t, d) => d.substs.find(_.name == t))
      .flatMap(s => s.param.zip(s.term).map((p, l) => Binding(p, () => l.value)))
  def opCode(kb: FrModel): List[Binding] = opBindings(kb)((_, i) => () => i.factory())

  /** By the code of the first contract on each operation that has some. */
  private def opBindings(kb: FrModel)(bind: (Node[?], Implementation) => () => Any): List[Binding] =
    kb.onOp.toList.sortBy(_._1).flatMap { (_, ns) =>
      (for c <- ns; op <- c.op; i <- kb.implementation(c) yield Binding(op, bind(c, i))).take(1)
    }

  /** The assumptions of facts, to check where code runs; one over a quantifier cannot be computed: it is trusted only. */
  def runtimeAssumptions(kb: FrModel): List[Assumption] =
    kb.nodes.filter(_.kind == NodeKind.Assumption).flatMap { n =>
      n.formula.map { l =>
        val f = l.value.asInstanceOf[() => Boolean]
        Assumption(n.id, kb.reads(l).toSet, () => try f() catch case _: NotExecutable => true)
      }
    }
