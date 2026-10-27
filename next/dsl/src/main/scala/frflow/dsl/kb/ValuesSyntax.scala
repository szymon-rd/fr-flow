package frflow.dsl.kb

import frflow.core.code.Values
import frflow.dsl.vocab.Definition

/** `env(grants)` in plain code: a Definition's value among those the code is given, typed by its declaration. Only a
  * Definition is read: code never reads a Declaration.
  */
object ValuesSyntax:
  extension (env: Values)
    def apply[A](d: Definition[A]): A =
      env.get(d.name).getOrElse(throw IllegalStateException(s"${d.name.value} is not given to this code"))
        .asInstanceOf[A] // given under its own declaration's name, typed `A`
