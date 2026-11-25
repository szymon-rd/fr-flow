package frflow.core.normal

import frflow.core.effect.{ClassName, EType, FieldOf, MethodName, OutsideOf}

/** A method of the code read, normalised: what it is given, the type of what it gives, and its body. The object
  * it is called on is `Atom.Self` in the body. A class's constructor is one, named `new`.
  */
final case class NormalMethod(name: MethodName, params: List[(Local, EType)], gives: EType, body: Block)

/** Normalised Scala (`docs/EFFECT-TREES.md`, 4.2): the code after the rewrites Scala's definition prescribes and
  * before any interpretation. Typed, in statement form, with every operand an atom, so that the order of
  * evaluation is the order of the statements. Plain data: it refers to no compiler and no prover.
  */
final case class NormalProgram(sources: List[String], classes: List[ClassName], fields: List[FieldOf],
    methods: List[NormalMethod], outside: List[OutsideOf])
