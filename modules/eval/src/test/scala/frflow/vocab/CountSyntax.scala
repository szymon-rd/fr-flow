package frflow.vocab

import frflow.core.term.{Bound, Sym}
import frflow.dsl.build.Source
import frflow.dsl.term.{LeanType, Notes, Term}

/** `xs.count(x => p)` as a model writes it, with `import frflow.vocab.CountSyntax.*`: built as the core's binders
  * are (`Terms`), its body a host function given each interpreter's own variable.
  */
object CountSyntax:
  extension [A: LeanType](xs: Term[List[A]])
    inline def count(inline p: Term[A] => Term[Boolean]): Term[BigInt] =
      counted(xs, Source.of(p).params.headOption.getOrElse("x"), p)

  private def counted[A: LeanType](xs: Term[List[A]], hint: String, p: Term[A] => Term[Boolean]): Term[BigInt] =
    Term.noted(Notes.of(LeanType[A].declares))([T[_]] => (s: Sym[T]) =>
      Count.in(s).count(xs.run(s), Bound[A](hint, LeanType[A].ty))(Term.body(s, p)))
