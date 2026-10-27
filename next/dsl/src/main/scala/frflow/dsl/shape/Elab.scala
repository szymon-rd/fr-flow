package frflow.dsl.shape

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Lambda}
import frflow.core.name.SourceText
import frflow.core.spec.Written
import frflow.dsl.build.{AsWritten, Declarations, Deferred, ElabError, Failure, Fault, Site}
import frflow.dsl.flow.{ReadRecording, Recorded}
import frflow.dsl.term.{LeanType, Notes, Term}

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
      (t.notes, Written.lambda(xs, t.run, SourceText(written.text)))
    }

  /** A program's lambda: its body the steps recorded on its inputs' variables, bound at levels `0 … n-1`. */
  def program[R](at: Site, inputs: List[LeanType[?]], r: LeanType[R])(body: Vector[Binder] => Recorded[Term[R]],
      written: AsWritten): Deferred[Written[Lambda]] =
    made(at, inputs) { () =>
      val xs = inputs.zipWithIndex.map((t, i) => DefineShape.binder(i, t, written.params))
      val (prog, notes) = ReadRecording(body(xs.toVector))
      (notes |+| Notes.of(r.declares), Written.steps(xs, prog, r.ty, SourceText(written.text)))
    }

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
