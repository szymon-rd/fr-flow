package frflow.dsl.lifted

import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** A call of an ordinary method of the developer's (a case class's member, an object's function) in lifted code:
  * its body read where it is called, as an `inline def`'s is, its receiver the body's `this` and its arguments its
  * parameters. The compiler shows a macro the body of a method it is not given only when it kept it: the project
  * compiles with `-Yretain-trees`; without it the call is not read, and the error says so. A method that calls
  * itself is a recursion, which is not read.
  */
private[lifted] trait ReadMethods extends Reading:
  this: Reader =>
  import q.reflect.*

  def method(t: Term, as: TypeRepr)(using env: Env)(using Quotes): Option[Expr[DTerm[?]]] =
    val (fn, args) = applied(t, Nil)
    val m = fn.symbol
    kept(m).map { d =>
      if env.reading(m) then refuse(s"`${m.name}` calling itself: recursion is not read yet", t)
      val params = d.termParamss.flatMap(_.params)
      if params.size != args.size then refuse(s"this call of `${m.name}`", t)
      val given_ = params.zip(args).map((p, a) => (p.symbol, read(a, p.tpt.tpe)))
      val self = fn match
        case Select(on, _) if !on.symbol.flags.is(Flags.Module) => List((m.owner, read(on, on.tpe.widen)))
        case _                                                  => Nil
      read(d.rhs.get, as)(using env.entering(m) ++ given_ ++ self)
    }

  /** The method's definition with its body, when it is the developer's and the compiler kept it. */
  def kept(m: Symbol): Option[DefDef] =
    Option.when(isOwn(m))(m.tree).collect { case d: DefDef if d.rhs.nonEmpty => d }

  /** A method of the developer's code: no library's, none the compiler made. */
  def isOwn(m: Symbol): Boolean =
    !m.isNoSymbol && m.isDefDef && !m.flags.is(Flags.Synthetic) && !m.flags.is(Flags.Inline) &&
      !List("scala.", "java.").exists(m.fullName.startsWith)

  /** A function applied to every argument list it is given. */
  private def applied(t: Term, args: List[Term]): (Term, List[Term]) = t match
    case Apply(f, more)  => applied(f, more ++ args)
    case TypeApply(f, _) => applied(f, args)
    case other           => (other, args)
