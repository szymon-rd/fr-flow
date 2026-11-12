package frflow.core.spec

import frflow.core.name.SymbolName
import frflow.core.expr.Lambda

/** A formula read as a call of one Definition on its leading variables (`granted(held, request) === …`): the post a
  * test checks a call of that Definition's code against. Derived from the formula (`CallForms`), never written.
  */
final case class CallForm(definition: SymbolName, posted: Written[Lambda])
