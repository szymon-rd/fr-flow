package frflow.dsl.lifted

import scala.quoted.*

/** A compile error where a type's equality is not data's (`FrSpec.derived`): a spec is of a type whose `==` is the
  * compiler's, so equal values are equal terms.
  */
object Structural:
  inline def check[T]: Unit = ${ data[T] }

  def data[T: Type](using q: Quotes): Expr[Unit] =
    import q.reflect.*
    val own = TypeRepr.of[T].classSymbol.toList.flatMap(c => c :: c.children).exists(c =>
      c.isClassDef && !List("scala.", "java.").exists(c.fullName.startsWith) &&
        c.declaredMethod("equals").exists(m => !m.flags.is(Flags.Synthetic)))
    if own then report.errorAndAbort(s"FrFlow: ${Type.show[T]} declares its own `equals`, so it can have no " +
      "FrSpec: a value of code FrFlow reads is data, equal exactly when its parts are")
    '{ () }
