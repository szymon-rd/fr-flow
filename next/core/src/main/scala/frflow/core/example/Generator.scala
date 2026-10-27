package frflow.core.example

import frflow.core.ty.Ty

/** A generator the model gives for a type (`kb.generating(gen)`). */
final case class Generator[T](ty: Ty, gen: Gen[T])
