package frflow.core.staged

import frflow.core.code.Datum

/** An expression staged (`Meaning.denote_step`): the program its tree means, with what the meaning reads of the
  * tree and of the scope read here.
  */
private[staged] trait StageExprs extends StageBase:
  import Tree.*

  /** What a call is given: a tree to evaluate, or a value it already is. */
  type Given = Either[V, Tree]

  def applied(f: Tree, targs: List[Datum], args: List[Given])(using Env): P
  def select(on: P, s: Sym, targs: List[Datum], args: List[Given])(using Env): P
  def ident(s: Sym, targs: List[Datum], args: List[Given])(using Env): P
  def function(d: DefDef, group: List[DefDef])(using Env): V
  def matched(v: V, cases: List[Tree])(using Env): P
  def tried(t: Try)(using Env): P

  def expr(t: Tree)(using e: Env): P = t match
    case Literal(c)                => constant(c)
    case Ident(s)                  => ident(s, Nil, Nil)
    case Select(on, s)             => select(expr(on), s, Nil, Nil)
    case This(cls)                 => thisOf(cls)
    case Apply(f, args)            => applied(f, Nil, args.map(Right(_)))
    case TypeApply(f, targs)       => applied(f, targs, Nil)
    case Typed(x, _)               => expr(x)
    case Block(stats, result)      => block(stats)(inner => expr(result)(using inner))
    case Inlined(bindings, body)   => block(bindings)(inner => expr(body)(using inner))
    case If(c, a, b)               => bind(expr(c), "test")(v => P.Truth(v, expr(a), expr(b)))
    case While(c, body)            => op("while_", Arg.Prog(expr(c)), Arg.Prog(expr(body)))
    case Assign(to, rhs)           => assigned(to, rhs)
    case Match(on, cases)          => bind(expr(on), "matched")(v => matched(v, cases))
    case t: Try                    => tried(t)
    case Return(x, from)           => bind(expr(x), "returned")(v => op("return_", value(v), Arg.Text(from.key)))
    case Closure(Ident(s))         => closure(s.key)
    case Repeated(elems)           => each(elems.map(expr), "elem")(vs => P.Give(V.Many(vs)))
    case other                     => P.Stuck(unmeant(other))

  private def unmeant(t: Tree): String = t match
    case New(_)                 => "a class made with no constructor called"
    case Closure(_)             => "a function value of what is no function made here"
    case Unmeant("Super")       => "a member of a parent, called past this class's own"
    case Unmeant("SelectOuter") => "a member of an enclosing object, reached from inside"
    case Unmeant("SummonFrom")  => "a choice made by the compiler where the code is inlined"
    case _                      => "a tree that is no expression"

  private def constant(c: Datum): P = c match
    case Datum.Of("CFloat" | "CDouble", _) => P.Stuck("a floating-point constant")
    case Datum.Of("CUnit", _)              => P.Give(V.Unit)
    case _                                 => P.Give(V.Const(c))

  /** `this` of the class `cls` (`Meaning.this_val`). */
  def thisOf(cls: String)(using e: Env): P = table.classOf(cls) match
    case Some(c) if table.isModule(c) => op("module_obj", Arg.Text(cls))
    case Some(_)                      => read(s"this:$cls") match
      case P.Stuck(_) => P.Stuck(s"this, of a class the code is not in: $cls")
      case found      => found
    case None                         => P.Stuck(s"this, of a class that is not the program's: $cls")

  private def closure(key: String)(using e: Env): P = e.bound.get(key) match
    case Some(Bound.Made(v, _)) => P.Give(v)
    case Some(_)                => P.Stuck(s"a function value that is not in scope: $key")
    case None                   => e.rest.fold(P.Stuck(s"a function value that is not in scope: $key"))(sc =>
      op("function_sought", variable(sc), Arg.Text(key)))

  /** The statements of a block in order, then what follows them in the scope they leave. */
  def block(stats: List[Tree])(next: Env => P)(using e: Env): P = stats match
    case Nil        => next(e)
    case st :: rest => st match
      case ValDef(s, flags, t, Some(rhs)) =>
        if flags.contains("Lazy") then refuse("a lazy value made in a method")
        bind(expr(rhs), s.key.takeWhile(_ != '#'))(v =>
          if !flags.contains("Mutable") then block(rest)(next)(using e.having(s.key, Bound.Plain(v)))
          else
            val cell = op("new_var", Arg.Text(Defined.tyClass(t).fold("<var>")("<var>:" + _)), value(v))
            bind(cell, s.key.takeWhile(_ != '#'))(r => block(rest)(next)(using e.having(s.key, Bound.Held(r)))))
      case ValDef(s, _, _, None)          => P.Stuck(s"a value with no right side: ${s.key}")
      case d: DefDef                      =>
        val x = e.names.fresh(d.s.key.takeWhile(_ != '#'))
        val made = function(d, (st :: rest).collect { case g: DefDef => g })
        P.Let(x, made, block(rest)(next)(using e.having(d.s.key, Bound.Made(V.Var(x), d))))
      case _: ClassDef | Unmeant("TypeDef" | "Imported" | "Exported") => block(rest)(next)
      case other                          => after(expr(other))(block(rest)(next))

  private def assigned(to: Tree, rhs: Tree)(using e: Env): P = to match
    case Ident(s: Sym.Local)              => e.bound.get(s.key) match
      case Some(Bound.Held(cell)) => bind(expr(rhs), "value")(v => op("set_var", value(cell), value(v)))
      case Some(_)                => P.Stuck(s"an assignment to what is no variable: ${s.key}")
      case None                   => e.rest.fold(P.Stuck(s"an assignment to what is no variable: ${s.key}"))(sc =>
        bind(expr(rhs), "value")(v => op("assign_sought", variable(sc), Arg.Text(s.key), value(v))))
    case Ident(Sym.Member(owner, name, _)) =>
      bind(thisOf(owner), "this")(on => bind(expr(rhs), "value")(v =>
        op("set_field", value(on), Arg.Text(name), value(v))))
    case Ident(Sym.NoSym)                 => P.Stuck("an assignment to nothing")
    case Select(on, Sym.Member(_, name, _)) =>
      bind(expr(on), "on")(o => bind(expr(rhs), "value")(v => op("set_field", value(o), Arg.Text(name), value(v))))
    case _                                => P.Stuck("an assignment to what is neither a variable nor a field")
