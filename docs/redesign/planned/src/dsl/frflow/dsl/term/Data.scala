package frflow.dsl.term

/** The companion of a case class or an enum built from terms (`object Claims extends Data[Claims]`): its `LeanType`
  * derived (with the type's declaration and `DataRep`), and its constructor on terms (`Claims(r, u, rs)`).
  */
trait Data[T]:
  inline given leanType: LeanType[T] = ${ DataMacros.derived[T] }
