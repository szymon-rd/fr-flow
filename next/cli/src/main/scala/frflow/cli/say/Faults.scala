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
    case Site.Model(m)    => s"the model ${m.value}"
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
    case Fault.OutsideStep            => "a program's step is used outside a program"
    case Fault.NotATerm(what)         => s"a program's step gives $what, which is not a term: Lean cannot read it"

  /** A fault in what gives a Definition its meaning: its model, its Scala, its proven code. */
  private val meaning: PartialFunction[Fault, String] =
    case Fault.NotAnOperation(what)   => s"a program's step $what applies no Definition: a step is an operation on a " +
        "state applied (inRoom(request.room))"
    case Fault.NotOneModel(ds)        => s"implementTested is given ${ds.mkString(", ")}, which are not operations " +
        "one model gives a meaning"
    case Fault.OperationsMissing(m, ds) => s"the Scala of $m's operations is given without ${ds.mkString(", ")}: " +
        "give each one"
    case Fault.ModelledElsewhere(d)   => s"$d is an operation on a state, its meaning its model's: give its Scala " +
        "with implementTested"
    case Fault.MeantByTwo(d, ms)      => s"$d is given a meaning by two models (${ms.mkString(", ")})"
    case Fault.ProgramMentioned(p)    => s"the program $p is mentioned in a statement: it is the meaning " +
        "implementProven gives the Definition; speak of the Definition"
    case Fault.NotProvenCode(d)       => s"implementProven is given $d, which is not a define or a program"
    case Fault.MeantWhereWritten(d)   => s"$d has its meaning where it is written (a define, a program): it is " +
        "given another"
    case Fault.Thrown(message)        => s"building it threw: $message"

  /** A value only plain code reads, spoken of in a statement. */
  def codeOnly(scalaType: String): String =
    s"$scalaType has no LeanType: add `derives LeanType` if a statement should speak of it"

  private def invalid(i: RelPath.Invalid): String = i match
    case RelPath.Invalid.Absolute(_)       => "it is absolute (paths are relative to the project)"
    case RelPath.Invalid.OutsideProject(_) => "it leads out of the project"
    case RelPath.Invalid.Empty             => "it is empty"
