package frflow.proof.rocq

import frflow.core.code.Datum
import frflow.core.staged.{Arg, Handler, Kept, P, StagedCode, StagedUnit, UnitKind, V}

/** Staged code as one Rocq file over `FrFlow/Code/Staged.v`: the definitions function values hold in place of
  * their trees, each unit's program, and `Code_units`, which gives a unit by what is called.
  */
object StagedModule:
  private val header =
    """From Stdlib Require Import String List ZArith.
      |Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
      |Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
      |Require FrFlow.Code.Staged.
      |Import ListNotations.
      |Open Scope string_scope.
      |Open Scope meaning_scope.""".stripMargin

  def apply(code: StagedCode): String =
    val stubs = code.units.flatMap(u => held(u.body)).distinct.zipWithIndex.map((d, i) => d -> s"stub_${i + 1}").toMap
    val values = PrintStagedValues(stubs)
    val programs = PrintStaged(values)
    val units = code.units.map(u => unit(u, programs(u.body)))
    val held_ = stubs.toList.sortBy(_._2.drop(5).toInt).map(stub).mkString("\n\n")
    List(left(code), header, held_, "Section Units.\n\n  Variable T : table.", units.mkString("\n\n"),
      table(code.units, values), "End Units.", outside(code, values)).filter(_.nonEmpty).mkString("\n\n") + "\n"

  /** What was not staged, and why: the meaning of its tree answers for it. */
  private def left(code: StagedCode): String =
    val each = code.unstaged.map((what, why) => s"    - $what: $why")
    (s"(** Staged: ${code.units.size} programs. Left to the meaning of the tree: ${code.unstaged.size}." :: each)
      .mkString("\n") + " *)"

  /** What the staging took of the definitions from outside, and that the library says the same. */
  private def outside(code: StagedCode, values: PrintStagedValues): String =
    val each = code.outside.map((s, taken) => s"(${values.sym(s)}, ${taken.mkString("[", "; ", "]")})")
    s"""(** The definitions from outside the code calls, each with the arguments the staging took it to take
       |    unevaluated: the library says the same of each. *)
       |Definition Code_outside : list (sym * list bool) :=
       |  ${each.mkString("[", ";\n   ", "]")}.
       |
       |Lemma Code_outside_agrees : forallb (fun taken => Staged.takes (fst taken) (snd taken)) Code_outside = true.
       |Proof. vm_compute. reflexivity. Qed.""".stripMargin

  private def stub(d: Datum, name: String): String = s"Definition $name : tree :=\n${PrintData(d, 2)}."

  private def unit(u: StagedUnit, body: List[String]): String =
    val given_ = u.kind match
      case UnitKind.Method(_) | UnitKind.Init(_) => "(this : val) (args : list val)"
      case UnitKind.Function(_)                  => "(sc : scope) (args : list val)"
      case UnitKind.ByName(_)                    => "(sc : scope)"
    (s"  Definition ${u.name} $given_ : D :=" :: body.map("    " + _)).mkString("\n") + "."

  /** Which unit answers a call: by the definition's name, or the class's. */
  private def table(units: List[StagedUnit], values: PrintStagedValues): String =
    def chosen(of: List[(String, String)]): List[String] =
      of.map((test, name) => s"      if $test then Some $name else") :+ "      None"
    def by(kind: PartialFunction[UnitKind, String], over: String): List[String] =
      s"    (fun $over =>" :: (chosen(units.flatMap(u => kind.lift(u.kind).map(_ -> u.name))).init :+ "      None)")
    val methods = by({ case UnitKind.Method(s) => s"sym_eqb s ${values.sym(s)}" }, "s")
    val inits = by({ case UnitKind.Init(c) => s"String.eqb cls \"$c\"" }, "cls")
    val functions = by({ case UnitKind.Function(s) => s"sym_eqb s ${values.sym(s)}" }, "s")
    val byName = by({ case UnitKind.ByName(s) => s"sym_eqb s ${values.sym(s)}" }, "s")
    ("  Definition Code_units : Staged.units := Staged.Units" :: methods ::: inits ::: functions ::: byName)
      .mkString("\n") + "."

  /** The definitions the function values of a program hold. */
  private def held(p: P): List[Datum] = p match
    case P.Give(v)                 => inValue(v)
    case P.Bind(_, of, next)       => held(of) ++ held(next)
    case P.Let(_, v, next)         => inValue(v) ++ held(next)
    case P.Op(_, args)             => args.flatMap(inArg)
    case P.Truth(v, yes, no)       => inValue(v) ++ held(yes) ++ held(no)
    case P.Parts(of, _, found, no) => held(of) ++ held(found) ++ held(no)
    case P.Share(_, shared, next)  => held(shared) ++ held(next)
    case P.Given(_, body)          => held(body)
    case P.Handle(body, h, last)   => held(body) ++ h.toList.flatMap(inHandler) ++ last.toList.flatMap(held)
    case P.Use(_) | P.Stuck(_)     => Nil

  private def inHandler(h: Handler): List[Datum] = held(h.body)

  private def inKept(k: Kept): List[Datum] = k.entries.flatMap((_, v) => inValue(v))

  private def inValue(v: V): List[Datum] = v match
    case V.Function(stub, kept) => stub :: inKept(kept)
    case V.ByName(_, kept)      => inKept(kept)
    case V.Many(vs)             => vs.flatMap(inValue)
    case _                      => Nil

  private def inArg(a: Arg): List[Datum] = a match
    case Arg.Val(v)       => inValue(v)
    case Arg.Vals(vs)     => vs.flatMap(inValue)
    case Arg.Prog(p)      => held(p)
    case Arg.Scope(k)     => inKept(k)
    case Arg.Lazily(each) => each.flatMap(_.fold(inValue, held))
    case _                => Nil
