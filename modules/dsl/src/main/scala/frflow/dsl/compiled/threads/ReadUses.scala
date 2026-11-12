package frflow.dsl.compiled.threads

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
