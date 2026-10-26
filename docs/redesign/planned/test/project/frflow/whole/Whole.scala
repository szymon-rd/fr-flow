package whole

import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.example.Example
import frflow.core.name.DefName
import frflow.dsl.kb.KnowledgeBase
import frflow.eval.Semantics
import frflow.proof.lean.ast.{Decl, LeanName, Names}
import frflow.proof.lean.lower.{LowerEnv, LowerProp, LowerWitness, Naming}
import frflow.proof.lean.print.PrintDecl
import frflow.proof.layout.WholeModule
import frflow.proof.obligation.{Constant, Obligation}
import frflow.proof.whole.{ExampleGoals, Joint, Possible}
import frflow.proof.terms.TermTable
import frflow.testing.search.Witnesses

/** A knowledge base's theory-level obligations as `project.pipeline.Analysis` makes them (the witnesses searched
  * for as `program.RunScala` does), and their Lean as `Whole.lean` declares it.
  */
final class Whole(kb: KnowledgeBase, examples: List[Example]):
  private val e = kb.elaborated.fold(es => throw AssertionError(es.toString), identity)
  val resolved: Resolved = Resolve(Validate(e).fold(ps => throw AssertionError(ps.toString), identity))
  val table: TermTable = TermTable.of(resolved)
  private val search = Witnesses(Semantics(e), resolved.theory, _ => Nil)
  val found = frflow.core.consistency.Consistency.vacuity(resolved.theory)
    .flatMap(v => search.of(v).map(v -> _.map(Constant(_, _)))).toMap
  val obligations: List[Obligation] =
    Joint.of(resolved) ++ Possible.of(resolved, found) ++ ExampleGoals.of(resolved, examples)

  private val env = LowerEnv(e.theory.name, opens, _ => Names.builtin("store"), _ => Names.builtin("Bookings"),
    n => e.theory.vocabulary.dataType(n))
  private val naming = Naming.over(e.theory.vocabulary.symbols.map(_.name.value).toSet,
    e.theory.vocabulary.types.map(_.typeName.value).toSet + "World")

  /** Each declaration of `Whole.lean`, printed. */
  def lean: List[String] = WholeModule(LowerProp(table, env), LowerWitness(env, naming))
    .of(e.theory.name, Nil, obligations).decls.map(d => PrintDecl(d: Decl))

  private def opens(d: DefName): List[LeanName] =
    table.defines.get(d).toList.flatMap(_.symbols.map(s => Names.ident(s.value)))
