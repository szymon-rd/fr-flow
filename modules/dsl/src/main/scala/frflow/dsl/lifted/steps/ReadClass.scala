package frflow.dsl.lifted.steps

import frflow.dsl.lifted.{FrSpec, NotRead, Tasty}
import frflow.dsl.structure.StructureDeclaration
import frflow.dsl.term.{Lift, Term}
import scala.quoted.{Expr, Quotes, staging}
import scala.util.control.NonFatal

/** A compiled class read as the model is built, from the TASTy the compiler wrote beside its class file: no macro
  * where the class is lifted, and nothing the compiler must keep. A compiler is started over the class's own
  * classpath; it loads the class's tree (`Tasty`), the reader reads it as it reads a tree inside a compilation
  * (`StructureLift`), and what the reader writes is compiled and run here. So a class is read wherever its TASTy
  * is: in the project, or in a library's jar.
  */
object ReadClass:
  /** The class `cls`, which implements a structure, read: each member's code. `words` are the words of the
    * structures it holds, in the order its constructor takes them. Scala the reader does not read is a `NotRead`.
    */
  def structure[C](cls: Class[?], words: List[StructureDeclaration[?]]): StructureCode[C] =
    read(cls)(StructureLift.staged(cls.getName.replace('$', '.'), words))(words).asInstanceOf[StructureCode[C]]

  /** An object of a class that implements a structure, as a state of the structure: the record of its
    * constructor's fields (`StructureLift.state`), and the object's own values in it.
    */
  def held[S](made: Any): Term[S] =
    val state = read(made.getClass)(StructureLift.state(made)).asInstanceOf[FrSpec[Any]]
    Lift.constant[Any](StructureType.held(state, made))(using state).asInstanceOf[Term[S]] // typed by its name

  /** What `reading` writes of `cls`, compiled and run: by a compiler over the classpath `cls` was loaded from,
    * which keeps the trees it loads and admits what Scala marks experimental (capture checking's classes).
    */
  private def read[A](cls: Class[?])(reading: Quotes ?=> Expr[A]): A =
    given staging.Compiler.Settings = staging.Compiler.Settings.make(compilerArgs = List("-Yretain-trees",
      "-experimental"))
    given staging.Compiler = staging.Compiler.make(cls.getClassLoader)
    try staging.run((q: Quotes) ?=> reading(using Tasty.typing(q)))
    catch
      case refused: NotRead => throw refused
      case NonFatal(other)  => throw NotRead(s"FrFlow: ${cls.getName} is not read from its TASTy: $other")
