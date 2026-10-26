package frflow.project.pipeline

import frflow.core.analysis.{Premise, Resolve, Resolved}
import frflow.core.checking.Checking
import frflow.core.code.Code
import frflow.core.consistency.{Standing, Vacuity}
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.core.Theory
import frflow.core.ty.Ty

/** The content fields that render values: how a statement is checked, how the code stands, a store's model. Each one
  * function of the IR, written once for the new ledgers (today's renderings are a reference); the rebuilt examples'
  * goldens pin them.
  */
object Texts:
  /** `name: means` of every opaque type and Definition or Declaration the node speaks of, sorted: what its statement
    * mentions (through its defines).
    */
  def vocabulary(t: Theory, id: NodeId): List[String] =
    val (v, m) = (t.vocabulary, Resolve.mentions(t, id))
    (v.sorts.filter(s => m.types.contains(s.name)).map(s => s"${s.name.value}: ${s.means}") ++
      v.symbols.filter(s => m.symbols.contains(s.name)).map(s => s"${s.name.value}: ${s.means}")).sorted

  /** How the statement is checked, in words (`show` prints these beside it): read off its formula, its place and
    * what defines the Definitions it mentions (owner §15), since nothing of it is written beside the statement.
    */
  def checking(t: Theory, id: NodeId): List[String] = Checking.of(t, id).map(said)

  private def said(c: Checking): String = c match
    case Checking.FromParts(ps)        => s"proven from its parts (${names(ps.map(_.value))})"
    case Checking.AgainstCode(d, code) => against(d.value, code)
    case Checking.TestedAgainst(d, w)  => s"tested against ${d.value}'s Scala on generated cases" +
      (if w then ", the statement evaluated whole" else "")
    case Checking.NotTested(d)         =>
      s"not checked against ${d.value}'s Scala: the statement has no Scala value (it quantifies over every value)"
    case Checking.AssumedByCallers(ds) => s"assumed by the code calling ${names(ds.map(_.value))}"
    case Checking.WhereMade(ty, ds, ms) =>
      val makers = ds.map(_.value) ++ ms.map((m, op) => s"${m.value}'s ${op.value}")
      s"met where a ${typeName(ty)} is made" + (if makers.isEmpty then "" else s" (${names(makers)})") +
        s"; assumed of every ${typeName(ty)} in Lean"
    case Checking.KeptBy(ds)           => s"kept by every run of ${names(ds.map(_.value))}, from the state it starts in"
    case Checking.RestsOn(p, by)       => s"rests on ${premise(p)}: " + by.fold("not assumed")(_.value)
    case Checking.Consistent(g, s)     => s"consistent with ${names(g.map(_.value))}: ${standing(s)}"
    case Checking.Possible(vs)         => s"not vacuous: ${vs.map(vacuity).mkString(", ")}"
    case Checking.Trusted              => "trusted"
    case Checking.Outside(f)           => outside(f)
    case Checking.StoreCodeTested(n)   => s"the store's code tested against the model ($n implementations)"
    case Checking.Unchecked            => "not checked yet: no parts, no code"

  private def against(d: String, code: Code): String = code match
    case Code.Proven(c)     => s"proven of $d's code, ${c.value}"
    case Code.ProvenFlow(c) => s"proven of $d's program, ${c.value}"
    case Code.Tested(_, _)  => s"tested against $d's Scala on generated cases"
    case Code.Valued(_)     => s"proven of $d's value"
    case Code.Provided      => s"stated for every value of $d provided where the code runs"

  private def premise(p: Premise): String = p match
    case Premise.BehavesAs(m)     => s"the store behaving as ${m.value}"
    case Premise.OneRunAtATime(m) => s"one run at a time on ${m.value}"
    case Premise.Initially(m)     => s"the state ${m.value} starts in"
    case Premise.WrittenOnlyBy(m) => s"who writes ${m.value}"
    case Premise.Calls(d)         => s"what the outside calls ${d.value} with"

  private def outside(f: OutsideFact): String = f match
    case OutsideFact.BehavesAs(b, m)      => s"the world outside: ${b.value} behaves as ${m.value}"
    case OutsideFact.WrittenOnlyBy(m, ps) => s"the world outside: only ${names(ps.map(_.value))} write ${m.value}"
    case OutsideFact.OneRunAtATime(m)     => s"the world outside: runs on ${m.value} never interleave"
    case OutsideFact.Initially(m, _)      => s"the world outside: the state ${m.value} starts in"
    case OutsideFact.Calls(d)             => s"the world outside: ${d.value} is called with values that can be made"

  private def standing(s: Standing): String = s match
    case Standing.Witnessed      => "witnessed, for Lean to check"
    case Standing.Evidence(ts)   => s"evidence only (${names(ts.map(_.value))} tested), consistency not proven"
    case Standing.Unwitnessed(_) => "consistency not proven"

  private def vacuity(v: Vacuity): String = v match
    case Vacuity.Inhabited(_, ty)      => s"some ${typeName(ty)} meets it"
    case Vacuity.Satisfiable(_, i, _)  => s"condition ${i + 1} can hold"

  private def names(ns: List[String]): String = if ns.isEmpty then "none yet" else ns.mkString(", ")
  private def typeName(ty: Ty): String = Ty.names(ty).headOption.fold(ty.toString)(_.value)

  def implementation(r: Resolved, id: NodeId): Option[String] = ???
  def model(r: Resolved, id: NodeId): Option[List[String]] = ???
  def implementations(r: Resolved, id: NodeId): Option[List[String]] = ???
