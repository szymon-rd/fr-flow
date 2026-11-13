package frflow.cli.say

import frflow.core.name.RelPath
import frflow.dsl.build.{ElabError, Fault, Site}

/** What keeps a FrModel, or its examples, from elaborating, in words: where, then what. */
object Faults:
  def text(e: ElabError): String = s"${site(e.at)}: ${fault(e.fault)}"

  def site(s: Site): String = s match
    case Site.Node(id)    => s"node $id"
    case Site.Define(d)   => s"the define ${d.value}"
    case Site.Meaning(s)  => s"the meaning given ${s.value}"
    case Site.Example(n)  => s"the example \"$n\""

  def fault(f: Fault): String = (written orElse meaning)(f)

  /** A fault in what is written: a value, a type, a path, a step. */
  private val written: PartialFunction[Fault, String] =
    case Fault.DeclaredLater          => "a value is used before it is declared: declare it above"
    case Fault.NoType(where)          => s"$where has no type FrFlow can read"
    case Fault.FunctionEquality       => "two functions are compared: compare their results on every input instead"
    case Fault.NotData(value)         => s"$value is not data a statement can speak of"
    case Fault.NoField(name)          => s"the record has no field $name"
    case Fault.CodeOnlyInStatement(t) => codeOnly(t)
    case Fault.BadPath(path, why)     => s"$path is not a path in the project: ${invalid(why)}"
    case Fault.NotAClaim(what)        => s"$what is not a claim: only a claim is left open above"
    case Fault.AlwaysInside           => "always is a node's whole formula: inside another (under forall, !, " +
        "implies, ||, or in a define) it would range over every value Rocq has; use forall there"

  /** A fault in what gives a Definition its meaning: its model, its Scala, its proven code. */
  private val meaning: PartialFunction[Fault, String] =
    case Fault.NotProvenCode(d)       => s"define is given $d, which is not a define or a program"
    case Fault.MeantWhereWritten(d)   => s"$d has its meaning where it is written (a define, a program): it is " +
        "given another"
    case Fault.NoContract(t)          => s"$t's FrSpec states no contract: state one where the spec is given " +
        "(`FrSpec.derived[…].where(v => …)`)"
    case Fault.Thrown(message)        => s"building it threw: $message"
    case Fault.HeldByTwo(s, holders)  => s"$s is read as it stands beside ${holders.mkString(" and ")}, which " +
      s"both hold one: say whose is meant (`$s.….in(${holders.head}.current)`)"
    case Fault.HeldTwice(s, ways)     => s"$s is held more than one way from there (${ways.map(_.mkString(" then "))
      .mkString("; ")}): say which is meant, one holder at a time (`$s.in(….in(…))`)"
    case Fault.ExampleSetsClash(n, cs) => s"the classes of examples ${cs.mkString(" and ")} are both named $n, " +
        "as their examples' theorems are: rename one"

  /** A value only plain code reads, spoken of in a statement. */
  def codeOnly(scalaType: String): String =
    s"$scalaType has no RocqType: add `derives RocqType` if a statement should speak of it"

  private def invalid(i: RelPath.Invalid): String = i match
    case RelPath.Invalid.Absolute(_)       => "it is absolute (paths are relative to the project)"
    case RelPath.Invalid.OutsideProject(_) => "it leads out of the project"
    case RelPath.Invalid.Empty             => "it is empty"
