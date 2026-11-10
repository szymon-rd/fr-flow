package frflow.testing

import frflow.core.Elaborated
import frflow.core.expr.{Lambda, Value}
import frflow.core.name.SymbolName
import frflow.core.spec.Written
import frflow.core.ty.Ty
import frflow.dsl.build.Declarations
import frflow.dsl.lifted.Lifted
import frflow.eval.{Env, EvalError, Fn, ScalaValue}
import frflow.eval.run.Wiring
import frflow.eval.term.Semantics
import frflow.testing.derive.Derive
import frflow.testing.report.{Drawn, Seed}
import scala.util.Try

/** Lifted code's Scala against the term read from it (`Lifted`'s law): on generated inputs, each meeting what always
  * holds of its type in the model, the Scala the JVM runs (`native`) gives what the evaluator gives of the term,
  * which is the term Lean is printed from. So the reader's translation of each function is tested, not trusted:
  * a construct it read as a term of another value shows as a case here. A Definition the code calls has the meaning
  * the model gives it. Case `i` is drawn from `(seed, i)` at its size, as a claim's are; the first case that differs
  * is the report.
  */
final class Agreement(e: Elaborated):
  def of(code: Lifted[?], settings: Settings): Agreement.Report = between(code, code, settings)

  /** The term read from one lifted function against the Scala of another of its type: of one function, its law
    * (`of`); of two, whether they are one function on the cases drawn.
    */
  def between[F](term: Lifted[F], scala: Lifted[F], settings: Settings): Agreement.Report =
    val read = term.onTheSpot.flatMap(_.lambda.run.toOption)
    Agreement.Report(term.name, read.fold(Agreement.Outcome.NotRead)((ds, w) => tested(scala, settings)(ds, w)))

  private def tested(code: Lifted[?], settings: Settings)(ds: Declarations, w: Written[Lambda]): Agreement.Outcome =
    val all = holding(ds)
    val (semantics, types) = (Semantics(all), w.value.params.map(_.ty))
    val (draw, term) = (Derive.of(all, Nil), semantics.lambda(w))
    val wiring = Wiring(semantics, all.theory)
    val meanings = Env.of(wiring.values(wiring.supplied(Nil)))
    val cases = Iterator.range(0, settings.cases).flatMap { i =>
      val from = Drawn(settings.seed, i, Seed.sizeOf(i, settings.cases))
      draw.all(types, from.size, from.seed.forCase(i)).map(_.map(ScalaValue(_)) -> from)
    }.toList
    val differ = cases.iterator.flatMap((args, from) => differing(code, term.run(meanings, _))(args).map(
      (scala, read) => Agreement.Outcome.Differ(args.zip(types).map(semantics.reflect), scala, read, from)))
    differ.nextOption().getOrElse(if cases.isEmpty then Agreement.Outcome.NoCases else
      Agreement.Outcome.Agree(cases.size))

  /** What the Scala and the term give on `args`, when they are not one value. */
  private def differing(code: Lifted[?], term: List[ScalaValue] => Either[EvalError, ScalaValue])(
      args: List[ScalaValue]): Option[(Agreement.Gave, Agreement.Gave)] =
    val scala = Try(Fn.call(Fn.ref(ScalaValue(code.native)), args)).toEither.left.map(String.valueOf(_))
    val read = term(args).left.map(_.toString)
    Option.when(scala != read)((scala.map(shown), read.map(shown)))

  private def shown(v: ScalaValue): String = String.valueOf(v.unwrap)

  /** The model with the types the code's inputs declare: a function no statement mentions yet is tested too. */
  private def holding(ds: Declarations): Elaborated =
    val more = ds.types.values.flatten.toList
    val v = e.theory.vocabulary
    e.copy(theory = e.theory.copy(vocabulary = v.copy(types = (v.types ++ more.map(_.data)).distinct)),
      reps = e.reps ++ more.map(d => d.data.typeName -> d.rep))

object Agreement:
  /** What the Scala or the term gave on a case: a value as printed, or why it gave none (what the Scala threw). */
  type Gave = Either[String, String]

  /** What testing one lifted function found. */
  final case class Report(code: SymbolName, outcome: Outcome):
    def agrees: Boolean = outcome match
      case Outcome.Agree(_) => true
      case _                => false

  enum Outcome:
    /** The Scala and the term gave one value on each of `cases` cases. */
    case Agree(cases: Int)
    /** The first case they differ on: its inputs, what each gave, and where it was drawn. */
    case Differ(inputs: List[Value], scala: Gave, term: Gave, from: Drawn)
    /** No case could be drawn (an input's type has no value meeting what always holds of it). */
    case NoCases
    /** The term does not elaborate: the model's errors say why. */
    case NotRead

  def of(e: Elaborated, settings: Settings)(codes: Lifted[?]*): List[Report] =
    val agreement = Agreement(e)
    codes.toList.map(agreement.of(_, settings))
