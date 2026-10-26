package frflow.decision.content

import cats.Eq

/** The hash of a node's governed code as the simple lexer reads it (`project.code.ScalaTokens`): comments stripped,
  * lines and indentation kept. The one form: the ledgers start fresh with it.
  */
final case class CodeFingerprint(sha: String)

object CodeFingerprint:
  given Eq[CodeFingerprint] = Eq.fromUniversalEquals
