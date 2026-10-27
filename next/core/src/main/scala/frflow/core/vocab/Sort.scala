package frflow.core.vocab

import frflow.core.name.TypeName

/** An opaque domain type (`Opaque("Realm", means)`): a Lean binder `(Realm : Type)` of every declaration that
  * mentions it, until a definition fixes it (`Realm := of[RealmId]`).
  */
final case class Sort(name: TypeName, means: String)
