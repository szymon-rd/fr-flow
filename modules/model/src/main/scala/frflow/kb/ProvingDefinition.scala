package frflow
package kb

/** `kb.implementProven(definition)(…)`: proven code, Lean proving it meets every claim on the Definition; `C` is a
  * flow's code, its steps from its inputs as terms.
  */
final class ProvingDefinition[F, C] private[frflow] (kb: FrModel, d: Definition[F]):
  inline def apply(inline impl: Def[F]): FrModel =
    kb.withDefinition(d, Implementation("", () => impl.lifted.value, Source.sourceFiles(impl), "", Some(impl)),
      leavesOnly = false)
  inline def apply(inline impl: C): FrModel =
    val failure = kb.claimsOn(d).flatMap(_.failure).headOption.map(_.err)
    val flow = Implementation.ofFlow(d, failure, impl.asInstanceOf[AnyRef], Source.text(impl), Source.sourceFiles(impl))
    kb.withDefinition(d, flow, leavesOnly = false)
