package frflow
package vocabulary

/** A domain term, open until a definition fixes it: a fact of the world, or an operation some contract is about.
  * It is a term: `grants.contains(g)`, `sessions(t)`. Plain code reads its value in force with `value`. One that only
  * code reads (a database connection) needs no Lean type: it cannot appear in a model.
  */
final class Param[A] @scala.annotation.publicInBinary private[frflow] (val name: String, val means: String)(using
    t: LeanType[A] = LeanType.unknown[A]) extends Term[A](null, t):
  override private[frflow] def termTree: Tree = Tree.Ref(this)
  def value: A = Bindings.get(this)
  inline def :=(inline v: Term[A]): Subst = Subst.term(this, Lifted.term(() => v, Source.text(v)))
  inline def :=[X, R](inline f: Term[X] => Term[R])(using x: LeanType[X]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x), Source.text(f)))
  inline def :=[X, Y, R](inline f: (Term[X], Term[Y]) => Term[R])(using x: LeanType[X], y: LeanType[Y]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y), Source.text(f)))
  inline def :=[X, Y, Z, R](inline f: (Term[X], Term[Y], Term[Z]) => Term[R])(using x: LeanType[X], y: LeanType[Y], z: LeanType[Z]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y, z), Source.text(f)))
  inline def :=[X, Y, Z, W, R](inline f: (Term[X], Term[Y], Term[Z], Term[W]) => Term[R])(using x: LeanType[X], y: LeanType[Y],
      z: LeanType[Z], w: LeanType[W]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y, z, w), Source.text(f)))
  inline def :=[X, Y, Z, W, V, R](inline f: (Term[X], Term[Y], Term[Z], Term[W], Term[V]) => Term[R])(using x: LeanType[X], y: LeanType[Y],
      z: LeanType[Z], w: LeanType[W], v: LeanType[V]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y, z, w, v), Source.text(f)))
  inline def :=[X, Y, Z, W, V, U, R](inline f: (Term[X], Term[Y], Term[Z], Term[W], Term[V], Term[U]) => Term[R])(using x: LeanType[X],
      y: LeanType[Y], z: LeanType[Z], w: LeanType[W], v: LeanType[V], u: LeanType[U]): Subst =
    Subst.term(this, Lifted.lambda(f, List(x, y, z, w, v, u), Source.text(f)))
  /** Evaluated on every use. */
  def bind(v: => A): Binding = Binding(this, () => v)
  /** `bind(table.get)`, with the table given to Lean too, so the examples are evaluated there. */
  def bindTable[K, V](table: Map[K, V])(using A =:= (K => Option[V])): Binding = Binding(this, () => table.get, Some(table))
  override def toString: String = name

object Param:
  /** `val granted = Param[(List[Booking], Booking) => Boolean]("whether a request is granted …")`: named `granted`. */
  inline def apply[A](means: String)(using t: LeanType[A] = LeanType.unknown[A]): Param[A] = new Param[A](Source.paramName, means)
