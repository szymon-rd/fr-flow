package frflow.dsl.kb

import cats.MonadThrow
import frflow.core.code.Implementation
import frflow.core.name.SourceText
import frflow.dsl.build.{Source, SourceFiles}
import frflow.dsl.node.Spans
import frflow.dsl.vocab.Definition

/** The Scala of operations on one state, waiting for each operation's function of the value `start` makes (`I`), its
  * type read off the operations' Definitions (`Shape.Scalas`): `t => (t.inRoom, t.add)`.
  */
final class Calls[G[_], I, Ss <: Tuple](kb: FrModel, ops: List[Definition[?]], ends: Calls.Ends, g: MonadThrow[G]):
  inline def apply(inline calls: I => Shape.Scalas[Ss, G]): FrModel =
    val names = ops.map(_.name)
    val scala = Implementation.Scala(ends.start, ends.observe, (i: Any) => calls(i.asInstanceOf[I]).toList)
    val files = Tested.files(ends.files ++ SourceFiles.of(calls))
    kb.implement(Operations(names, Implementation(names, scala, g,
      SourceText(s"(${ends.written})(${Source.of(calls).text})"), files), Spans.relative(Source.file)))

object Calls:
  /** How the Scala is made holding a state and read back, as written, and the files those refer to. The functions take
    * plain values of the model's state and of what `start` makes: the casts are of values `start` made or the model
    * holds, by the types `Tested` was typed with.
    */
  final case class Ends(start: Any => Any, observe: Any => Any, written: String, files: List[(String, List[String])])
