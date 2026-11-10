package frflow.dsl.lifted

import frflow.core.name.DefName
import frflow.dsl.build.{Source, WrittenAt}

/** `lifted { (a: A, b: B) => … }`: plain Scala as a Definition given its meaning where it is written. The compiler
  * reads the function's body into a term (`Reader`: a compile error on Scala outside what it reads), and the
  * function stays the Scala it is (`Lifted.native`). Every type of a value in it has an `FrSpec`. To four inputs.
  */
object LiftSyntax:
  inline def lifted[A: FrSpec, R: FrSpec](inline f: A => R): Lifted.Of1[A, R] =
    Lifted.Of1(Lifting.one[A, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read1[A, R](f)), f)

  inline def lifted[A: FrSpec, B: FrSpec, R: FrSpec](inline f: (A, B) => R): Lifted.Of2[A, B, R] =
    Lifted.Of2(Lifting.two[A, B, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read2[A, B, R](f)), f)

  inline def lifted[A: FrSpec, B: FrSpec, C: FrSpec, R: FrSpec](inline f: (A, B, C) => R): Lifted.Of3[A, B, C, R] =
    Lifted.Of3(Lifting.three[A, B, C, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read3[A, B, C, R](f)), f)

  inline def lifted[A: FrSpec, B: FrSpec, C: FrSpec, D: FrSpec, R: FrSpec](inline f: (A, B, C, D) => R)
      : Lifted.Of4[A, B, C, D, R] =
    Lifted.Of4(Lifting.four[A, B, C, D, R](DefName(Source.valName), WrittenAt.in(Source.here), Source.of(f))(
      LiftMacro.read4[A, B, C, D, R](f)), f)

  /** `always` of a type's contract, a node's whole formula: `Node.assumption("…")(contractOf[Booking])`. */
  export FrSpec.contractOf
