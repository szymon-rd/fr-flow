package frflow.project.pipeline

import frflow.core.analysis.{Premise, Resolve}
import frflow.core.checking.Checking
import frflow.core.code.Code
import frflow.core.consistency.{Standing, Vacuity}
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.core.Theory
import frflow.core.ty.Ty

/** The content fields that render the statement: its vocabulary, and how it is checked. Each one function of the IR,
  * written once for the new ledgers (today's renderings are a reference); the rebuilt examples' goldens pin them.
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
  def checking(t: Theory, id: NodeId): List[String] = Checking.of(t, id).map(c => (proven orElse world(id))(c))

  /** How it is proven or tested, and where its rule is met. */
  private val proven: PartialFunction[Checking, String] =
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
    case Checking.Unchecked            => "not checked yet: no parts, no code"

  /** What it says of a Declaration, the rules and the world it rests on, and its consistency. */
  private def world(id: NodeId): PartialFunction[Checking, String] =
    case Checking.SaysWhatIs(ds, code) => s"says what ${ds.map(_.value).mkString(", ")} " +
      (if ds.size == 1 then "is" else "are") + code.map((d, c) => s": ${d.value}'s ${kind(c)} stands in it").mkString
    case Checking.Rules(rs)            => "rules it uses: " + rs.map((r, taken) =>
      r.value + (if taken then "" else " (not taken)")).mkString(", ")
    case Checking.RestsOn(p, by)       => s"rests on ${premise(p)}: " + by.fold("not assumed")(_.value)
    case Checking.Consistent(g, s)     => g.filterNot(_ == id) match
        case Nil    => s"consistent: ${standing(s)}"
        case others => s"consistent with ${names(others.map(_.value))}: ${standing(s)}"
    case Checking.Possible(vs)         => s"not vacuous: ${vs.map(vacuity).mkString(", ")}"
    case Checking.Trusted              => "trusted"
    case Checking.Outside(f)           => outside(f)
    case Checking.ChangedBy(ps)        => s"the programs changing it, derived: ${names(ps.map(_.value))}"
    case Checking.StoreCodeTested(n)   => s"the store's code tested against the model ($n implementations)"

  /** What proven code is: `program, bookIfGranted`, `code, free`. */
  private def kind(code: Code): String = code match
    case Code.ProvenFlow(c) => s"program, ${c.value},"
    case Code.Proven(c)     => s"code, ${c.value},"
    case _                  => "value"

  private def against(d: String, code: Code): String = code match
    case Code.Proven(c)     => s"proven of $d's code, ${c.value}"
    case Code.ProvenFlow(c) => s"proven of $d's program, ${c.value}"
    case Code.Tested(_, _)  => s"tested against $d's Scala on generated cases"
    case Code.Valued(_)     => s"proven of $d's value"
    case Code.Provided      => s"stated for every value of $d provided where the code runs"

  private def premise(p: Premise): String = p match
    case Premise.BehavesAs(m)     => s"the store behaving as ${m.value}"
    case Premise.Atomic(b)        => s"runs on ${b.value} being atomic"
    case Premise.Initially(m)     => s"the state ${m.value} starts in"
    case Premise.FromOutside(ty)  => s"what each ${typeName(ty)} from outside meets"

  private def outside(f: OutsideFact): String = f match
    case OutsideFact.BehavesAs(b, m)      =>
      s"the world outside: ${b.value} does what ${m.value} does, and nothing outside the code changes it"
    case OutsideFact.Atomic(b)            => s"the world outside: runs on ${b.value} never interleave"
    case OutsideFact.Initially(m, _)      => s"the world outside: the state ${m.value} starts in"

  private def standing(s: Standing): String = s match
    case Standing.Witnessed      => "witnessed, for Lean to check"
    case Standing.Evidence(ts)   => s"evidence only (${names(ts.map(_.value))} tested), consistency not proven"
    case Standing.Unwitnessed(_) => "consistency not proven"

  private def vacuity(v: Vacuity): String = v match
    case Vacuity.Inhabited(_, ty)      => s"some ${typeName(ty)} meets it"
    case Vacuity.Satisfiable(_, i, _)  => s"condition ${i + 1} can hold"

  private def names(ns: List[String]): String = if ns.isEmpty then "none yet" else ns.mkString(", ")
  private def typeName(ty: Ty): String = Ty.names(ty).headOption.fold(ty.toString)(_.value)
