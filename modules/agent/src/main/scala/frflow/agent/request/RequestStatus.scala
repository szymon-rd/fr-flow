package frflow.agent
package request

import frflow.protocol.{Words, word}

enum RequestStatus:
  case Open, Answered, Closed
  override def toString: String = word(productPrefix)

object RequestStatus extends Words[RequestStatus]
