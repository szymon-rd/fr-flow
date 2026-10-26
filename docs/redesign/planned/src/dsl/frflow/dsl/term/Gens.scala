package frflow.dsl.term

import frflow.core.example.Gen

/** Generators as a model writes them: `Gens.derived[Session]` is every value of the type, made by `testing`. */
object Gens:
  def derived[A](using t: LeanType[A]): Gen[A] = Gen.Derived(t.ty)
