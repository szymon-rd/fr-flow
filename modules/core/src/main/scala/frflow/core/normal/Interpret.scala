package frflow.core.normal

import frflow.core.effect.{ClassName, EType, FieldName, MethodName, Prim}
import scala.collection.mutable

/** Normalised Scala run, one thread: what a method gives, as the statements say. It is what a rewrite of
  * normalised Scala is tested with (the same result before and after) and what the reading is compared with the
  * JVM by. A call outside the code, and an access of no object, do not run (`Stuck`).
  */
object Interpret:
  enum Value:
    case Whole(value: Int)
    case Truth(value: Boolean)
    case Nothing
    case NoObject
    case At(place: Int)

  final class Stuck(what: String) extends RuntimeException(what)

  /** What `method`, called on an object of its class just made and constructed with nothing, gives. */
  def scenario(p: NormalProgram, method: MethodName): Value =
    val run = Run(p)
    val made = run.make(method.cls)
    val _ = run.call(MethodName(method.cls, "new"), made, Nil)
    run.call(method, made, Nil)

  private final class Run(p: NormalProgram):
    private val heap = mutable.ArrayBuffer.empty[mutable.Map[FieldName, Value]]
    private val methods = p.methods.map(m => m.name -> m).toMap

    def make(cls: ClassName): Value =
      heap += mutable.Map.from(p.fields.filter(_.name.cls == cls).map(f => f.name -> initial(f.ty)))
      Value.At(heap.size - 1)

    def call(m: MethodName, on: Value, args: List[Value]): Value =
      val method = methods.getOrElse(m, throw Stuck(s"no method ${m.written}"))
      if on == Value.NoObject then throw Stuck(s"${m.written} called on no object")
      Frame(this, on, mutable.Map.from(method.params.map(_._1).zip(args))).block(method.body)

    def fieldsOf(on: Value, f: FieldName): mutable.Map[FieldName, Value] = on match
      case Value.At(n) if heap(n).contains(f) => heap(n)
      case _                                  => throw Stuck(s"${f.written} of what has none")

  private def initial(t: EType): Value = t match
    case EType.Int  => Value.Whole(0)
    case EType.Bool => Value.Truth(false)
    case EType.Unit => Value.Nothing
    case _          => Value.NoObject

  private final class Frame(run: Run, self: Value, locals: mutable.Map[Local, Value]):
    def block(b: Block): Value =
      b.stmts.foreach(stmt)
      atom(b.gives)

    private def atom(a: Atom): Value = a match
      case Atom.Of(l)    => locals(l)
      case Atom.Whole(n) => Value.Whole(n.toInt)
      case Atom.Truth(b) => Value.Truth(b)
      case Atom.Nothing  => Value.Nothing
      case Atom.NoObject => Value.NoObject
      case Atom.Self     => self

    private def stmt(s: Stmt): Unit = s match
      case Stmt.Val(l, _, r, _)  => locals(l) = rhs(r)
      case Stmt.Var(l, _, a)     => locals(l) = atom(a)
      case Stmt.Assign(l, a)     => locals(l) = atom(a)
      case Stmt.Write(on, f, v)  => run.fieldsOf(atom(on), f)(f) = atom(v)
      case Stmt.Loop(test, body) => while block(test) == Value.Truth(true) do block(body): Unit
      case Stmt.Run(r)           => rhs(r): Unit

    private def rhs(r: Rhs): Value = r match
      case Rhs.Is(a)                            => atom(a)
      case Rhs.Applied(op, args)                => Prims(op, args.map(atom))
      case Rhs.Read(on, f)                      => run.fieldsOf(atom(on), f)(f)
      case Rhs.Make(c)                          => run.make(c)
      case Rhs.Call(Kind.Static(m), on, args)   => run.call(m, atom(on), args.map(atom))
      case Rhs.Call(Kind.External(o), _, _)     => throw Stuck(s"${o.written} is outside the code")
      case Rhs.Choice(t, yes, no)               => block(if atom(t) == Value.Truth(true) then yes else no)

  /** An operation on values, as the JVM computes it: numbers wrap to 32 bits. */
  private object Prims:
    import Value.{Truth, Whole}

    def apply(op: Prim, to: List[Value]): Value = (op, to) match
      case (Prim.Add, List(Whole(a), Whole(b)))      => Whole(a + b)
      case (Prim.Sub, List(Whole(a), Whole(b)))      => Whole(a - b)
      case (Prim.Mul, List(Whole(a), Whole(b)))      => Whole(a * b)
      case (Prim.Neg, List(Whole(a)))                => Whole(-a)
      case (Prim.Less, List(Whole(a), Whole(b)))     => Truth(a < b)
      case (Prim.LessEq, List(Whole(a), Whole(b)))   => Truth(a <= b)
      case (Prim.More, List(Whole(a), Whole(b)))     => Truth(a > b)
      case (Prim.MoreEq, List(Whole(a), Whole(b)))   => Truth(a >= b)
      case (Prim.SameInt, List(Whole(a), Whole(b)))  => Truth(a == b)
      case (Prim.And, List(Truth(a), Truth(b)))      => Truth(a && b)
      case (Prim.Or, List(Truth(a), Truth(b)))       => Truth(a || b)
      case (Prim.Not, List(Truth(a)))                => Truth(!a)
      case (Prim.SameBool, List(Truth(a), Truth(b))) => Truth(a == b)
      case (Prim.SameRef, List(a, b))                => Truth(a == b)
      case _                                         => throw Stuck(s"$op applied to $to")
