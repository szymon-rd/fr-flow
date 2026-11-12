package frflow.dsl.compiled.threads

import frflow.dsl.compiled.threads.known.JdkOp

/** What a piece of code does with the variables in scope, read off its tree before it is read: the `var`s it
  * assigns and those it reads (a local method called counts for what it assigns and reads), whether it returns
  * from its method, and how it uses a value that may be null.
  */
private[threads] trait ReadUses extends ReadBlocks:
  import q.reflect.*

  def assigned(t: Tree)(using env: Env): List[Symbol] =
    val found = Assigned(env).foldTree(Set.empty, t)(Symbol.spliceOwner)
    env.declared.filter(found)

  /** The `var`s in scope that `t` reads or assigns, in the order they are declared. */
  def touched(t: Tree)(using env: Env): List[Symbol] =
    val found = Touched(env).foldTree(Set.empty, t)(Symbol.spliceOwner)
    env.declared.filter(found)

  def returns(t: Tree): Boolean = Returns.foldTree(false, t)(Symbol.spliceOwner)

  def effects(t: Tree)(using env: Env): Boolean = Effects(env).foldTree(false, t)(Symbol.spliceOwner)

  /** Whether what `rest` evaluates first is `v`, read where a null is no value: nothing happens between `v`'s
    * binding and that reading.
    */
  def readFirst(v: Symbol, rest: List[Tree]): Boolean =
    First(v).foldTrees(None, rest)(Symbol.spliceOwner).contains(true)

  /** Whether `t` names `sym`. */
  def names(t: Tree, sym: Symbol): Boolean = Named(sym).foldTree(false, t)(Symbol.spliceOwner)

  def uses(v: Symbol, rest: List[Tree]): List[Use] = Used(v).foldTrees(Nil, rest)(Symbol.spliceOwner)

  private final class Assigned(env: Env) extends TreeAccumulator[Set[Symbol]]:
    def foldTree(x: Set[Symbol], t: Tree)(owner: Symbol): Set[Symbol] = t match
      case Assign(lhs, rhs) => foldTree(x + lhs.symbol, rhs)(owner)
      case id: Ident        => env.vars.get(id.symbol) match
        case Some(Slot.Method(_, _, assigns)) => x ++ assigns
        case _                                => x
      case _                => foldOverTree(x, t)(owner)

  private final class Touched(env: Env) extends TreeAccumulator[Set[Symbol]]:
    def foldTree(x: Set[Symbol], t: Tree)(owner: Symbol): Set[Symbol] = t match
      case id: Ident => env.vars.get(id.symbol) match
        case Some(Slot.Method(_, vars, _)) => x ++ vars
        case Some(Slot.Mutable(_, _, _))   => x + id.symbol
        case _                             => x
      case _         => foldOverTree(x, t)(owner)

  private final class Effects(env: Env) extends TreeAccumulator[Boolean]:
    private def effect(c: Call): Boolean =
      scala.util.Try(opFor(c)).toOption.flatten.exists(op => !JdkOp.silent(op.name)) ||
        sigs.exists(_.sym == c.symbol) || c.name == "throw" || c.on.exists(q => isOpaque(plain(q.tpe).typeSymbol)) ||
        (c.name == "apply" && c.on.exists(q => isFunction(plain(q.tpe))))

    def foldTree(x: Boolean, t: Tree)(owner: Symbol): Boolean = t match
      case _ if x                                          => true
      case id: Ident if called(id)                         => true
      case New(tpt) if isOpaque(plain(tpt.tpe).typeSymbol) => true
      case term: Term if callOf(term).exists(effect)       => true
      case _                                               => foldOverTree(x, t)(owner)

    /** A by-name parameter, or a local method: reading it runs it. */
    private def called(id: Ident): Boolean = env.vars.get(id.symbol).exists {
      case Slot.ByName(_) | Slot.Method(_, _, _) => true
      case _                                     => false }

  /** What a piece of code evaluates first: `v` (true), or anything else that is no constant (false). */
  private final class First(v: Symbol) extends TreeAccumulator[Option[Boolean]]:
    def foldTree(x: Option[Boolean], t: Tree)(owner: Symbol): Option[Boolean] = (x, t) match
      case (Some(_), _)                                   => x
      case (_, id: Ident)                                 => Some(id.symbol == v)
      case (_, Literal(_))                                => x
      case (_, This(_) | New(_) | Try(_, _, _) | While(_, _) | Closure(_, _)) => Some(false)
      case (_, _: DefDef | _: ClassDef)                   => Some(false)
      case _                                              => foldOverTree(x, t)(owner)

  /** A `return` of the method `t` is in: one of a method declared inside `t` is that method's. */
  private object Returns extends TreeAccumulator[Boolean]:
    def foldTree(x: Boolean, t: Tree)(owner: Symbol): Boolean = t match
      case Return(_, _) => true
      case _: DefDef    => x
      case _            => foldOverTree(x, t)(owner)

  private final class Named(sym: Symbol) extends TreeAccumulator[Boolean]:
    def foldTree(x: Boolean, t: Tree)(owner: Symbol): Boolean = t match
      case id: Ident if id.symbol == sym => true
      case _                             => foldOverTree(x, t)(owner)

  private final class Used(v: Symbol) extends TreeAccumulator[List[Use]]:
    private def isNull(t: Tree): Boolean = t match
      case Literal(NullConstant()) => true
      case _                       => false
    private def isV(t: Tree): Boolean = t match
      case id: Ident => id.symbol == v
      case _         => false

    def foldTree(x: List[Use], t: Tree)(owner: Symbol): List[Use] = t match
      case Apply(Select(on, "==" | "!=" | "eq" | "ne"), List(n)) if isV(on) && isNull(n) => Use.Tested :: x
      case Match(on, cases) if isV(on) && cases.exists(c => isNull(c.pattern))          =>
        foldTrees(Use.Tested :: x, cases)(owner)
      case a: Apply if callOf(a).exists(givenNullable(_, v))                            =>
        val parts = callOf(a).toList.flatMap(c => c.on.toList ++ c.args).filterNot(isV)
        foldTrees(Use.Nullable :: x, parts)(owner)
      case _ if isV(t)                                                                  => Use.Other :: x
      case _                                                                            => foldOverTree(x, t)(owner)
