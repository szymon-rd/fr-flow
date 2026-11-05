package frflow.proof.lean.ast

/** One generated Lean file: its imports, preamble, namespace, the namespaces it opens inside, and its declarations. */
final case class LeanModule(name: ModuleName, imports: List[ModuleName], preamble: Preamble, namespace: List[LeanName],
    opens: List[List[LeanName]], decls: List[Decl])
