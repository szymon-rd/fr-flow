package frflow.core

import frflow.core.code.DataRep
import frflow.core.example.Generator
import frflow.core.name.TypeName

/** What elaboration gives: the theory, how Scala holds each domain type's values, and the generators given. */
final case class Elaborated(theory: Theory, reps: Map[TypeName, DataRep], generators: List[Generator[?]])
