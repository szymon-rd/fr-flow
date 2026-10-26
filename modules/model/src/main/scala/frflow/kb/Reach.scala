package frflow
package kb

/** Where a type's `always` rule applies within a value: to the value, to each element of a list, or within a field of
  * a record (every value of the type that can be made, wherever it is held).
  */
enum Reach:
  case It, Each
  case Field(name: String, index: Int, within: Reach)

  /** The rule `f` of `x` in Lean, where it applies. */
  def lean(x: String, f: String): String = this match
    case It                => s"($f $x)"
    case Each              => s"(∀ y ∈ $x, $f y)"
    case Field(n, _, rest) => rest.lean(if x.contains(' ') then s"($x).$n" else s"$x.$n", f)

  /** Whether `rule` holds of `v` where it applies, run as Scala. */
  def holds(v: Any, rule: Any => Boolean): Boolean = this match
    case It                => rule(v)
    case Each              => v.asInstanceOf[Iterable[Any]].forall(rule)
    case Field(_, i, rest) => rest.holds(v.asInstanceOf[Product].productElement(i), rule)
