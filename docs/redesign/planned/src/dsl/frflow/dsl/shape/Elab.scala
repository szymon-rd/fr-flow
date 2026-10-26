package frflow.dsl.shape

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.expr.{Expr, Exprs, Lambda}
import frflow.core.name.SourceText
import frflow.core.spec.Written
import frflow.dsl.build.{AsWritten, Declarations, Deferred, ElabError, Failure, Fault, Fresh, Site}
import frflow.dsl.term.{LeanType, Term}

/** The developer's lambdas, called once on fresh variables, as parts written at `at`: where their faults are placed. */
object Elab:
  def formula(at: Site, build: () => Term[Boolean], written: AsWritten): Deferred[Written[Expr]] =
    Deferred(guarded(at)(checked(at, build())).map(_.map(Written(_, SourceText(written.text)))))

  def lambda(at: Site, types: List[LeanType[?]])(call: List[Term[Any]] => Term[?], written: AsWritten)
      : Deferred[Written[Lambda]] =
    Deferred(guarded(at) {
      val xs = written.params.padTo(types.size, "x").zip(types.map(_.ty)).map(Fresh.binder)
      checked(at, call(xs.map(Term.variable))).map((ds, body) =>
        (ds |+| types.foldMap(_.declares), Written(Lambda(xs, body, Exprs.typeOf(body)), SourceText(written.text))))
    })

  private def checked(at: Site, t: Term[?]): ValidatedNec[ElabError, (Declarations, Expr)] =
    val errors = NonEmptyChain.fromChain(t.notes.faults.map(ElabError(at, _)))
    errors.fold(Validated.validNec((t.notes.declares, t.expr)))(Validated.invalid)

  private def guarded[A](at: Site)(a: => ValidatedNec[ElabError, A]): ValidatedNec[ElabError, A] =
    try a
    catch
      case f: Failure                     => ElabError(at, f.fault).invalidNec
      case scala.util.control.NonFatal(e) => ElabError(at, Fault.Thrown(String.valueOf(e.getMessage))).invalidNec
