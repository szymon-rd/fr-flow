package frflow.eval.term

import frflow.core.Booking
import frflow.core.term.Final
import frflow.core.ty.DataType
import frflow.proof.layout.LeanWorkspace
import frflow.proof.lean.ast.*
import frflow.proof.lean.laws.{LawsEnv, MoreTerms}
import frflow.proof.lean.lower.{LowerEnv, LowerType, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.Printed

/** The Lean of the law "Lean decides each term as the evaluator does": each term stated as the value Scala gives it
  * (the term, or its negation), in modules of at most 90 theorems over the laws' types, world (with faults) and
  * programs; and Lean's verdict on each theorem.
  */
object LawModules:
  /** The laws' environment, its world holding the faults beside `stored`, and `Spare` among its types. */
  val env: LowerEnv = LawsEnv.env.copy(faulty = true, models = List(Names.builtin("stored")),
    data = n => (List(Booking.data, MoreTerms.event, Spare.data) ++ DslTerms.types).find(_.typeName == n))
  /** As a FrModel's: no variable takes the FrModel's namespace, a program's name, or a name Lean writes itself. */
  private val naming = Naming.over(Set("Laws", "run", "attempt") ++ frflow.core.analysis.Reserved.names,
    Set(Booking.name.value, MoreTerms.eventName.value, "World", "Spare") ++ DslTerms.types.map(_.typeName.value))
  private val tactics =
    List("first", "  | decide", "  | frflow_eval", "  | (simp only [frflow_defs]; decide)",
      "  | simp_all [frflow_defs]")

  private def n(s: String): LeanName = Names.builtin(s)
  private def x(s: String, t: LExpr): LBinder = LBinder.Explicit(Names.ident(s), t)
  private def fields(d: DataType): List[(LeanName, LExpr)] = d match
    case DataType.Product(_, _, fs) => fs.map(f => Names.ident(f.name) -> LowerType(f.ty))
    case _                          => Nil
  private val types: List[Decl] = List(
    Decl.Structure(n("Booking"), fields(Booking.data)), Decl.Structure(n("Spare"), fields(Spare.data)),
    Decl.Inductive(n("Event"), List(n("Booked") -> List(x("at", LExpr.Name(n("Int")))), n("Cleared") -> Nil)),
    Decl.Structure(n("World"), List(n("stored") -> LExpr.Name(n("Int")), n("faults") -> LExpr.App(n0("List"),
      List(n0("Bool"))))),
    Decl.Def(List(Attr.FrflowDefs), n("positive"), Nil, LowerType.binder(frflow.core.expr.Terms.fnTy),
      Printed.formula(env, naming)(frflow.core.expr.Terms.positive.body))) ++ LawPrograms.decls ++
    DslTerms.decls(env, naming)
  private def n0(s: String): LExpr = LExpr.Name(n(s))

  /** The term as `holds` says: itself when true, its negation when false. */
  private def theorem(t: Final[Boolean], holds: Boolean, i: Int): Decl =
    val term = Printed.formula(env, naming)(t)
    val statement = if holds then term else LExpr.Prefix(LPrefix.NotSpaced, LExpr.Paren(term))
    Decl.Theorem(Nil, n(s"t_$i"), Nil, statement, Proof.Tactics(tactics), Break.SameLine)

  private val base = ModuleName(Names.path("FrFlowGen", "Laws", "Base"))
  private def module(name: ModuleName, imports: List[ModuleName], decls: List[Decl]): LeanModule =
    LeanModule(name, ModuleName(Names.path("FrFlow")) :: imports, Preamble.generated, Names.path("Laws"), Nil, decls)

  /** Whether Lean proves each term stated with its value, in order; and Lake's output. */
  def verdicts(name: String, stated: List[(Final[Boolean], Boolean)]): (List[Boolean], String) =
    val chunks = stated.zipWithIndex.grouped(90).toList.zipWithIndex.map((chunk, i) =>
      module(ModuleName(Names.path("FrFlowGen", "Laws", s"$name$i")), List(base),
        chunk.map { case ((t, v), j) => theorem(t, v, j) }))
    val (_, out) = LeanWorkspace.make(name.toLowerCase).build(module(base, Nil, types) :: chunks)
    (chunks.flatMap(m => proven(m, out)), out)

  /** For each theorem of `m`, in order, whether Lake's output has no error inside it. */
  private def proven(m: LeanModule, out: String): List[Boolean] =
    val lines = Print.module(m).linesIterator.toList
    val starts = lines.zipWithIndex.collect { case (l, i) if l.startsWith("theorem t_") => i + 1 }
    val file = m.name.file.value.stripPrefix("lean/")
    val errors = s"""error: ${java.util.regex.Pattern.quote(file)}:(\\d+):""".r.findAllMatchIn(out)
      .map(_.group(1).toInt).toList
    starts.zip(starts.drop(1) :+ Int.MaxValue).map((from, to) => !errors.exists(e => e >= from && e < to))
