package frflow.dsl.compiled

import frflow.dsl.term.Term as DTerm

/** A call of an ordinary method of the developer's (a class's member, an object's function): its body read where
  * it is called, its receiver the body's `this` and its arguments its parameters. The body is the method's tree
  * in the TASTy read. A method that calls itself is a recursion, which is not read.
  */
private[compiled] trait CompileMethods extends Compiling:
  this: Compiler =>
  import q.reflect.*

  def method(t: Term, as: TypeRepr)(using env: Env): Option[DTerm[Any]] =
    val (fn, args) = applying(t, Nil)
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

  /** The method's definition with its body, when it is the developer's and its TASTy is read. */
  def kept(m: Symbol): Option[DefDef] =
    Option.when(isOwn(m))(m.tree).collect { case d: DefDef if d.rhs.nonEmpty => d }

  /** A method of the developer's code: no library's, none the compiler made. An `inline def` is one: the TASTy is
    * written before the compiler puts its body where it is called, so its call is there as any other.
    */
  def isOwn(m: Symbol): Boolean =
    !m.isNoSymbol && m.isDefDef && !m.flags.is(Flags.Synthetic) &&
      !List("scala.", "java.").exists(m.fullName.startsWith)

  /** A function applied to every argument list it is given. */
  private def applying(t: Term, args: List[Term]): (Term, List[Term]) = t match
    case Apply(f, more)  => applying(f, more ++ args)
    case TypeApply(f, _) => applying(f, args)
    case other           => (other, args)
