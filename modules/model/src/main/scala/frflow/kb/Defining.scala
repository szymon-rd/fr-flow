package frflow
package kb

/** `kb.implementTested(definition)(code)`: plain Scala, a function of the Definition's inputs, tested against the
  * claims on it that nothing below proves.
  */
final class Defining[F] private[frflow] (kb: FrModel, d: Definition[F], calls: List[String]):
  inline def apply(inline impl: F): FrModel =
    kb.withDefinition(d, Implementation("", () => impl, Source.sourceFiles(impl), Source.sources(impl).mkString,
      calls = calls), leavesOnly = true)
