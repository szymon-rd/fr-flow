package frflow.lift

import frflow.ir.{IrCodec, LiftResult, Lifted}

/** A Scala value together with its FrFlow translation.
  *
  * `value` is the compiled Scala code, executed by the runtime; `ir` is the same
  * code as FrFlow IR, from which Lean is generated. Both come from one source
  * expression, so the executed code and the verified code cannot diverge.
  */
final class Code[+F](thunk: () => F, chunks: List[String]):
  /** The Scala value. Evaluated on first use: specification-only code is never run. */
  lazy val value: F = thunk()
  lazy val ir: LiftResult = IrCodec.decodeChunks(chunks)
  def lifted: Lifted = ir.lifted.getOrElse(throw IllegalStateException("not a lifted expression"))

object Code:
  /** Lifts a Scala expression, usually a lambda. Unsupported constructs are compile errors. */
  inline def apply[F](inline f: F): Code[F] = ${ LiftMacro.liftCode('f) }

/** The FrFlow translation of a Scala type (an ADT and everything it refers to). */
final class Schema[T](chunks: List[String]):
  lazy val ir: LiftResult = IrCodec.decodeChunks(chunks)

object Schema:
  inline given derived[T]: Schema[T] = ${ LiftMacro.schema[T] }
