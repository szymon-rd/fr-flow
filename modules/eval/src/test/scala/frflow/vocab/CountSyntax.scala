package frflow.vocab

import frflow.core.term.Bound
import frflow.core.term.language.Sym
import frflow.dsl.build.Source
import frflow.dsl.term.{RocqType, Notes, Term}

/** `xs.count(x => p)` as a model writes it, with `import frflow.vocab.CountSyntax.*`: built as the core's binders
  * are (`Terms`), its body a host function given each interpreter's own variable.
  */
object CountSyntax:
  extension [A: RocqType](xs: Term[List[A]])
    inline def count(inline p: Term[A] => Term[Boolean]): Term[BigInt] =
      counted(xs, Source.of(p).params.headOption.getOrElse("x"), p)

  private def counted[A: RocqType](xs: Term[List[A]], hint: String, p: Term[A] => Term[Boolean]): Term[BigInt] =
    Term.noted(Notes.of(RocqType[A].declares))([T[_]] => (s: Sym[T]) =>
      Count.in(s).count(xs.run(s), Bound[A](hint, RocqType[A].ty))(Term.body(s, p)))
