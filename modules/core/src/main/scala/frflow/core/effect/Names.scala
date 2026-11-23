package frflow.core.effect

/** A class of the code read, by a name no other class of the program has. */
final case class ClassName(value: String)

/** A field, by its class and its name there. */
final case class FieldName(cls: ClassName, name: String)

/** A method, by its class and a name no other method of the class has (one of several of a name is numbered). */
final case class MethodName(cls: ClassName, name: String)

/** What the code calls of code that is not read, by what declares it and a name no other member there has. */
final case class OutsideName(owner: String, name: String)
