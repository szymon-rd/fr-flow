package frflow.dsl.shape

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Exprs, Lambda, Quantifier}
import frflow.core.name.SourceText
import frflow.core.spec.Written
import frflow.dsl.build.{AsWritten, Declarations, Deferred, ElabError, Failure, Fault, Site}
import frflow.dsl.vocab.ReadRecording
import frflow.dsl.term.{LeanType, Notes, Term}
import frflow.core.term.interpret.Collect
import frflow.dsl.run.{Recorded, RunNote}
import frflow.dsl.vocab.Called

/** The developer's formulas and lambdas, built once, as parts written at `at`, where their faults are placed: each
  * kept as its term with the IR the analyses read (`Written`). A lambda's inputs are bound at levels `0 … n-1` and its
  * body read below them, so every binder in it is bound once: no numbering, no capture check.
  */
object Elab:
  def formula(at: Site, build: () => Term[Boolean], written: AsWritten): Deferred[Written[Expr]] =
    made(at) { () =>
      val t = build()
      (t.notes, Written.formula(t.run, SourceText(written.text)))
    }

  def lambda(at: Site, types: List[LeanType[?]])(build: () => (List[Binder], Term[?]), written: AsWritten)
      : Deferred[Written[Lambda]] =
    made(at, types) { () =>
      val (xs, t) = build()
      (t.notes, Written.lambda(xs, valued(t).run, SourceText(written.text)))
    }

  /** A define's body is a value: no rule (`always`, a node's whole formula) and no run (a statement's, of its own
    * variables) is written in it.
    */
  private def valued[A](t: Term[A]): Term[A] =
    Collect.of(t.run).collectFirst { case r: RunNote => r }.foreach(r =>
      throw Failure(Fault.RunInside(Called.of(r.program).fold("a program")(_._1.value))))
    if Term.exprOf(t).exists(e => Exprs.all(e).exists {
        case Expr.Quant(Quantifier.Always, _, _) => true
        case _                                   => false
      }) then throw Failure(Fault.AlwaysInside)
    t

  /** A program's lambda: its body the steps recorded on its inputs' variables, bound at levels `0 … n-1`. */
  def program[R](at: Site, inputs: List[LeanType[?]], r: LeanType[R])(body: List[Term[?]] => Recorded[?],
      written: AsWritten): Deferred[Written[Lambda]] =
    made(at, inputs) { () =>
      val xs = inputs.zipWithIndex.map((t, i) => DefineShape.binder(i, t, written.params))
      val (prog, notes) = ReadRecording.steps(body(xs.zip(inputs).map((x, t) => Term.free(x)(using t))))
      (notes |+| Notes.of(r.declares), Written.steps(xs, prog, r.ty, SourceText(written.text)))
    }

  /** A part built from recorded steps (a model's meanings), its notes' faults placed at `at`. */
  def recorded[A](at: Site)(build: () => (Notes, A)): Deferred[A] = made(at)(build)

  private def made[A](at: Site, types: List[LeanType[?]] = Nil)(build: () => (Notes, A)): Deferred[A] =
    Deferred(guarded(at) {
      val (notes, a) = build()
      checked(at, notes).map(ds => (ds |+| types.foldMap(_.declares), a))
    })

  private def checked(at: Site, notes: Notes): ValidatedNec[ElabError, Declarations] =
    NonEmptyChain.fromChain(notes.faults.map(ElabError(at, _)))
      .fold(Validated.validNec(notes.declares))(Validated.invalid)

  private def guarded[A](at: Site)(a: => ValidatedNec[ElabError, A]): ValidatedNec[ElabError, A] =
    try a
    catch
      case f: Failure                     => ElabError(at, f.fault).invalidNec
      case scala.util.control.NonFatal(e) => ElabError(at, Fault.Thrown(String.valueOf(e.getMessage))).invalidNec
