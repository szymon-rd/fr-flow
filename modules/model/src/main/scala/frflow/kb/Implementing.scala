package frflow
package kb

/** `kb.implementTested(contract)(code)`: the code is a Scala function of the operation's inputs. */
final class Implementing[F] private[frflow] (kb: FrModel, contract: Node[F], calls: List[String]):
  inline def apply(inline impl: F): FrModel =
    kb.withImplementation(Implementation(contract.id, () => impl, Source.sourceFiles(impl), Source.sources(impl).mkString,
      calls = calls))
