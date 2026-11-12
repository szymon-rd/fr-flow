package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Term as Rocq, Ty}
import frflow.dsl.compiled.threads.known.{Jdk, JdkOp}

/** A call of a method of the JDK: `call` of the operation `Jdk.methods` gives it, the object it is called on its
  * first argument where the operation takes it. A concurrent set's operation is chosen by what the set holds
  * (`Ts…`, `Es…`, `Vs…`); its `forEach` is a traversal (`ReadClosures`).
  */
private[threads] trait ReadOps extends ReadCalls:
  import q.reflect.*

  /** `set.forEach(fn)`, by the traversal `name` of a set of `of`s (`ReadClosures`). */
  def traversal(name: String, set: Term, fn: Term)(using Env): Res

  /** The operation a call is, if it is one of the JDK's. */
  def opFor(c: Call): Option[JdkOp] =
    val static = (c.symbol.owner.fullName.stripSuffix("$"), c.name)
    c.fn match
      case Select(New(tpt), _)         => Jdk.methods.get((plain(tpt.tpe).typeSymbol.fullName, "<init>"))
      case _ if static == Jdk.NewSet   => c.types.headOption.flatMap(t => Jdk.set(c.name, repr(t)))
      case Select(qual, _)             => setOf(qual.tpe) match
        case Some(of) => Jdk.set(c.name, of)
        case None     => bases(plain(qual.tpe).typeSymbol).collectFirst(Function.unlift(b =>
          Jdk.methods.get((b.fullName, c.name)))).orElse(Jdk.methods.get(static))
      case _                           => Jdk.methods.get(static)

  def op(c: Call)(using Env): Option[Res] = c.on.flatMap(set => setOf(set.tpe).map(set -> _)) match
    case Some((set, of)) if c.name == "forEach" => (Jdk.traversal(of), c.args) match
      case (Some(name), List(fn)) => Some(traversal(name, set, fn))
      case _                      => refuse("a traversal of a set of the JDK that is not read")
    case _                                      => opFor(c).map(operation(c, _))

  private def operation(c: Call, op: JdkOp)(using Env): Res =
    val on = if op.on == JdkOp.On.First then c.on.toList else Nil
    val (steps, terms) = values(arguments(on ++ c.args, op.takes))
    Res(steps, Rocq.of("call", Rocq.of(op.name, terms.map(bare)*)), op.gives, Res.Kind.Program)

  /** Where `v` is given to an operation of the JDK that takes a value that may be null. */
  def givenNullable(c: Call, v: Symbol): Boolean = scala.util.Try(opFor(c)).toOption.flatten.exists { op =>
    val on = if op.on == JdkOp.On.First then c.on.toList else Nil
    (on ++ c.args).zip(op.takes).exists {
      case (id: Ident, Ty.Of("option", _)) => id.symbol == v
      case _                               => false } }
