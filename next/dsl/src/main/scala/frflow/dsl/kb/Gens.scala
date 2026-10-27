package frflow.dsl.kb

import frflow.core.example.Gen
import frflow.dsl.term.LeanType

/** Generators as a model writes them: `Gens.derived[Session]` is every value of the type, made by `testing`. */
object Gens:
  def derived[A](using t: LeanType[A]): Gen[A] = Gen.Derived(t.ty)
