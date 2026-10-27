package frflow.proof.lean.ast

/** A declaration or command of a generated module. Declarations are separated by a blank line (`Print.module`). */
enum Decl:
  case Documented(doc: String, decl: Decl)
  case Def(attrs: List[Attr], name: LeanName, params: List[LBinder], ty: LExpr, body: LExpr)
  case Abbrev(attrs: List[Attr], name: LeanName, value: LExpr)
  case Theorem(attrs: List[Attr], name: LeanName, params: List[LBinder], statement: LExpr, proof: Proof, break: Break)
  case Structure(name: LeanName, fields: List[(LeanName, LExpr)])
  case Inductive(name: LeanName, ctors: List[(LeanName, List[LBinder])])
  case Class(name: LeanName, params: List[LBinder], ops: List[(LeanName, LExpr)])
  case Instance(cls: LExpr, fields: List[InstanceField])
  case Namespace(name: List[LeanName], decls: List[Decl])
  /** `frflow_match_eqns`: a match's equations made where it is declared. */
  case MatchEqns
  /** `set_option maxHeartbeats N in decl`: a try within its budget. */
  case Budgeted(heartbeats: Int, decl: Decl)
  /** `#print axioms N`: the audit of an authored proof's axioms. */
  case PrintAxioms(name: List[LeanName])
