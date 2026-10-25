package frflow
package kb

/** `kb.implementProven(contract)(…)`: `C` is a flow's code, its steps from its inputs as terms. */
final class Proving[F, C] private[frflow] (kb: KnowledgeBase, contract: Node[F]):
  inline def apply(inline impl: Def[F]): KnowledgeBase =
    kb.withImplementation(Implementation(contract.id, () => impl.lifted.value, Source.sourceFiles(impl), "", Some(impl)))
  inline def apply(inline impl: Def[F], inline runs: F): KnowledgeBase =
    kb.withImplementation(Implementation(contract.id, () => runs, Source.sourceFiles(runs), Source.sources(runs).mkString, Some(impl)))
  inline def apply(inline impl: C): KnowledgeBase =
    kb.withImplementation(Implementation.ofFlow(contract, impl.asInstanceOf[AnyRef], Source.text(impl), Source.sourceFiles(impl)))
