package frflow.core.effect

/** A field of a class: its type, which is what reading it gives. */
final case class FieldOf(name: FieldName, ty: EType)

/** A method of the code read: its inputs (the object it is called on first, `this`), what it gives, its tree. A
  * class's constructor is one, named `new`: called on the object just made.
  */
final case class MethodOf(name: MethodName, inputs: List[(String, EType)], gives: EType, body: Tree)

/** Something the code calls that is not read: what it takes and gives, and how Scala names it. */
final case class OutsideOf(name: OutsideName, takes: List[EType], gives: EType, scala: String)

/** Code read as trees of effects: where it was read from (its classes, by their full names), its classes, their
  * fields and methods, and what it calls outside itself, each named once. What `FrFlow/Effect` is instantiated
  * with for this code, and each method's tree.
  */
final case class Program(sources: List[String], classes: List[ClassName], fields: List[FieldOf],
    methods: List[MethodOf], outside: List[OutsideOf])
