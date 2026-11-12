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
    case Fault.RunInside(p)           => s"a run of $p is of a variable bound inside the statement: a run is of the " +
        "statement's own variables, from the world it holds in"
    case Fault.WorldRead(where)       => s"$where reads the world: it reads state through its own values and operations"
    case Fault.ReadTwoWays(p)         => s"a run of $p is read both as failing and plainly: read it as failing " +
        "everywhere in the statement, or nowhere"
    case Fault.RuleOverChanging(d, r, b) => s"the rule $r reads $d, which changes with the World ($b reads it " +
        "beside the World): a rule holds of values, in no world"
    case Fault.AlwaysInside           => "always is a node's whole formula: inside another (under forall, !, " +
        "implies, ||, or in a define) it would range over every value Lean has; use forall there"
    case Fault.AfterOfTwo(a, b)       => s"the worlds after a run of $a and a run of $b are read in one statement: " +
        "both runs are from the world it holds in, not one after the other; write a program that does both"
    case Fault.WorldUnnamed(vs)       => s"${vs.mkString(", ")} read the world without naming it in a statement " +
        "that reads a run: name it, t.current before the run or t.in(p.after) after it"
    case Fault.InNamed(what)          => s".in(…) $what: it reads no world it could read in another; .in reads in " +
        "a world after only what reads the world unnamed (a Declaration, a define reading state)"
    case Fault.ConstantInside(where)  => s"isConstant $where: it says that no run changes a value, so it is stated, " +
        "or under a condition (c implies t.isConstant), only"

  /** A fault in what gives a Definition its meaning: its model, its Scala, its proven code. */
  private val meaning: PartialFunction[Fault, String] =
    case Fault.NotAnOperation(what)   => s"a program's step $what applies no Definition: a step is an operation on a " +
        "state applied (inRoom(request.room))"
    case Fault.NotOneModel(ds)        => s"defineOperations is given ${ds.mkString(", ")}, which are not operations " +
        "one model gives a meaning"
    case Fault.OperationsMissing(m, ds) => s"the Scala of $m's operations is given without ${ds.mkString(", ")}: " +
        "give each one"
    case Fault.ModelledElsewhere(d)   => s"$d is an operation on a state, its meaning its model's: give its Scala " +
        "with defineOperations"
    case Fault.MeantByTwo(d, ms)      => s"$d is given a meaning by two models (${ms.mkString(", ")})"
    case Fault.ProgramMentioned(p)    => s"the program $p is mentioned in a statement: it is the meaning " +
        "a Declaration is given (book.define(…)); speak of that word"
    case Fault.NotProvenCode(d)       => s"define is given $d, which is not a define or a program"
    case Fault.MeantWhereWritten(d)   => s"$d has its meaning where it is written (a define, a program): it is " +
        "given another"
    case Fault.NoContract(t)          => s"$t's FrSpec states no contract: state one where the spec is given " +
        "(`FrSpec.derived[…].where(v => …)`)"
    case Fault.Thrown(message)        => s"building it threw: $message"
    case Fault.HeldByTwo(s, holders)  => s"$s is read as it stands beside ${holders.mkString(" and ")}, which " +
      s"both hold one: say whose is meant (`$s.….in(${holders.head}.current)`)"
    case Fault.ExampleSetsClash(n, cs) => s"the classes of examples ${cs.mkString(" and ")} are both named $n, " +
        "as their examples' theorems are: rename one"

  /** A value only plain code reads, spoken of in a statement. */
  def codeOnly(scalaType: String): String =
    s"$scalaType has no LeanType: add `derives LeanType` if a statement should speak of it"

  private def invalid(i: RelPath.Invalid): String = i match
    case RelPath.Invalid.Absolute(_)       => "it is absolute (paths are relative to the project)"
    case RelPath.Invalid.OutsideProject(_) => "it leads out of the project"
    case RelPath.Invalid.Empty             => "it is empty"
