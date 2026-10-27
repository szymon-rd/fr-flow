package frflow.proof.layout

import frflow.core.name.{DefName, NodeId}
import frflow.proof.lean.ast.{Decl, LeanModule, LeanName, ModuleName}

/** A module's imports, read off what its declarations use (`Mentioned`): the domain's types always; a define's
  * module for each define it calls; a node's module for each of its declarations or theorems it names; the
  * boundaries for the world, a model or a boundary's class.
  */
object Imports:
  def of(l: Lowering, decls: List[Decl], self: ModuleName): List[ModuleName] =
    (l.layout.types :: Mentioned.of(decls).flatMap(module(l, _))).distinct.filterNot(_ == self)

  /** The module, its imports read off its declarations. */
  def onto(l: Lowering, m: LeanModule): LeanModule = m.copy(imports = of(l, m.decls, m.name))

  private def module(l: Lowering, path: List[LeanName]): Option[ModuleName] =
    val kb = l.kb.value
    path.map(_.text.stripPrefix("«").stripSuffix("»")) match
      case List(`kb`, d) if l.isDefine(d)                         => Some(l.layout.define(DefName(d)))
      case `kb` :: n :: "Proofs" :: _ if l.node(NodeId(n))        => Some(l.layout.proofs(NodeId(n)))
      case `kb` :: n :: part :: _ :: Nil if l.node(NodeId(n))     =>
        NodePart.values.find(_.toString == part).map(l.layout.ofNode(NodeId(n), _))
      case List(`kb`, n, _) if l.node(NodeId(n))                  => Some(l.layout.ofNode(NodeId(n), NodePart.Spec))
      case `kb` :: m :: _ if l.isModelSpace(m)                    => Some(l.layout.boundaries)
      case c :: _ if l.isBoundaryClass(c) || c == "World"         => Some(l.layout.boundaries)
      case `kb` :: "Whole" :: _                                   => Some(l.layout.whole)
      case _                                                      => None
