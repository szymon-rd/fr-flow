package frflow.decision.content

import cats.Eq

/** The hash of a node's governed code: of its tokens and layout (`Tokens`), or of its raw text (`Text`, before). */
enum CodeFingerprint:
  case Text(sha: String)
  case Tokens(sha: String)

  def stored: String = this match
    case Text(sha)   => sha
    case Tokens(sha) => s"tokens:$sha"

object CodeFingerprint:
  def read(s: String): CodeFingerprint = if s.startsWith("tokens:") then Tokens(s.drop(7)) else Text(s)
  given Eq[CodeFingerprint] = Eq.fromUniversalEquals
