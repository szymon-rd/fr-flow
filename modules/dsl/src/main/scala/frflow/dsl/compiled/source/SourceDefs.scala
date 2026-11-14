package frflow.dsl.compiled.source

import frflow.core.threads.Datum
import frflow.core.threads.Datum.{Many, Maybe, Text}
import frflow.dsl.lifted.NotRead

/** A definition as the tree read holds it: a value, a method (with the methods it overrides, which is what a call
  * of one of them on an object of this class runs), a type, a class (its constructor, its parents, its body).
  */
private[source] trait SourceDefs extends SourceTrees:
  import q.reflect.*

  def definition(d: Definition): Datum = d match
    case ValDef(_, of, rhs)           =>
      Datum.of("ValDef", sym(d.symbol), flags(d.symbol), ty(of.tpe), Maybe(rhs.map(tree)))
    case DefDef(_, clauses, of, rhs)  =>
      Datum.of("DefDef", sym(d.symbol), flags(d.symbol), Many(clauses.map(parameters)), ty(of.tpe),
        Maybe(rhs.map(tree)), Many(d.symbol.allOverriddenSymbols.toList.map(sym)))
    case TypeDef(name, rhs)           => Datum.of("TypeDef", Text(name), flags(d.symbol), denoted(rhs))
    case ClassDef(_, ctor, parents, self, body) =>
      Datum.of("ClassDef", Text(classKey(d.symbol)), flags(d.symbol), definition(ctor), trees(parents),
        Maybe(self.map(definition)), trees(body))

  private def parameters(clause: ParamClause): Datum = clause match
    case TermParamClause(ps) => Many(ps.map(definition))
    case TypeParamClause(ps) => Many(ps.map(definition))

  /** The type a type definition's right side denotes. */
  private def denoted(rhs: Tree): Datum = rhs match
    case t: TypeTree       => ty(t.tpe)
    case t: TypeBoundsTree => ty(t.tpe)
    case other             => throw NotRead(s"FrFlow: a type definition whose right side is ${other.show}")
