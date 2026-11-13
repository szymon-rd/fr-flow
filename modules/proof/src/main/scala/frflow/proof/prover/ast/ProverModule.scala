package frflow.proof.prover.ast

/** One generated module: its imports, preamble, namespace, the namespaces it opens inside, and its declarations.
  *
  * The AST of this package is in Lean's syntax, kept from when Lean was the prover. It has two readers: a node's
  * signed content is its text (`term.Print`), so no decision is reopened by the move to Rocq, and Rocq is printed
  * from it (`proof.rocq`). Where this package and `core.name.ProverNames` say Lean, they mean that syntax.
  */
final case class ProverModule(name: ModuleName, imports: List[ModuleName], preamble: Preamble,
    namespace: List[ProverName], opens: List[List[ProverName]], decls: List[Decl])
