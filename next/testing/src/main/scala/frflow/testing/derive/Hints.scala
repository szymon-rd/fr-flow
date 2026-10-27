package frflow.testing.derive

import frflow.core.example.{Gen, Generator}
import frflow.core.ty.Ty

/** What the model and its examples tell the derived generators: the generators given for some types
  * (`kb.generating(gen)`), and the examples' values (`Seeds`).
  */
final case class Hints(generators: List[Generator[?]], seeds: Seeds):
  def generatorFor(ty: Ty): Option[Gen[?]] = generators.find(_.ty == ty).map(_.gen)

object Hints:
  val none: Hints = Hints(Nil, Seeds.none)
