package frflow.dsl.flow

import scala.quoted.*

/** An instance of a boundary trait written by `BoundaryMacros`: `new B[F, V] { def op(p: V[A]) = … }`, each operation's
  * body made by `body` from the operation and its parameters' references, typed as the trait declares it.
  */
object BoundaryInstance:
  def of[B[_[_], _[_]]: Type, F[_]: Type, V[_]: Type](using q: Quotes)(ops: List[BoundaryTrait.Op])(
      body: (BoundaryTrait.Op, List[q.reflect.Term]) => q.reflect.Term): Expr[B[F, V]] =
    import q.reflect.*
    val iface = TypeRepr.of[B].appliedTo(List(TypeRepr.of[F], TypeRepr.of[V]))
    val declared = ops.map(o => o -> declaredOp(iface, o.name))
    val cls = Symbol.newClass(Symbol.spliceOwner, s"${iface.typeSymbol.name}Instance", List(TypeRepr.of[Object], iface),
      c => declared.map((o, m) => Symbol.newMethod(c, o.name, iface.memberType(m), Flags.Override, Symbol.noSymbol)),
      None)
    val defs = declared.map { (o, _) =>
      val m = cls.declaredMethod(o.name).head
      DefDef(m, argss => Some(body(o, argss.flatten.collect { case t: Term => t }).changeOwner(m)))
    }
    val made = Apply(Select(New(TypeIdent(cls)), cls.primaryConstructor), Nil)
    Block(List(ClassDef(cls, List(TypeTree.of[Object], Inferred(iface)), defs)), Typed(made, Inferred(iface)))
      .asExprOf[B[F, V]]

  private def declaredOp(using Quotes)(iface: quotes.reflect.TypeRepr, name: String): quotes.reflect.Symbol =
    import quotes.reflect.*
    iface.typeSymbol.declaredMethod(name) match
      case List(m) => m
      case _       =>
        report.errorAndAbort(s"FrFlow: ${iface.typeSymbol.name}.$name: a boundary's operations are not overloaded")
