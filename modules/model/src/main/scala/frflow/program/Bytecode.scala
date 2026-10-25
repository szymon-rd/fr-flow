package frflow
package program

import java.io.DataInputStream
import scala.util.Try

/** The methods a class declares, as its class file has them: what each method's code calls. Enough to tell the
  * `equals` Scala generates for a case class (it reads every field) from one the program wrote.
  */
private[frflow] final class Bytecode private (methods: Map[(String, String), Array[Byte]], names: Int => Option[String]):
  def code(name: String, descriptor: String): Option[Array[Byte]] = methods.get((name, descriptor))

  /** The names of the methods a method's code calls (read from its invoke instructions' operands). */
  def calls(name: String, descriptor: String): Set[String] =
    code(name, descriptor).fold(Set.empty[String]) { c =>
      c.indices.filter(i => i + 2 < c.length && Bytecode.Invokes((c(i) & 0xff))).flatMap { i =>
        names(((c(i + 1) & 0xff) << 8) | (c(i + 2) & 0xff))
      }.toSet
    }

private[frflow] object Bytecode:
  private val Invokes = Set(0xb6, 0xb7, 0xb8, 0xb9)

  /** The class file of `c`, if its class loader can give it. */
  def of(c: Class[?]): Option[Bytecode] =
    Option(c.getClassLoader).flatMap(l => Option(l.getResourceAsStream(c.getName.replace('.', '/') + ".class")))
      .flatMap(s => Try { try read(DataInputStream(s)) finally s.close() }.toOption)

  private def read(in: DataInputStream): Bytecode =
    in.readInt(); in.readUnsignedShort(); in.readUnsignedShort()
    val n = in.readUnsignedShort()
    val utf8 = scala.collection.mutable.Map.empty[Int, String]
    val refs = scala.collection.mutable.Map.empty[Int, Int] // a method reference -> its name and type
    val nameAndType = scala.collection.mutable.Map.empty[Int, Int] // a name and type -> its name
    var i = 1
    while i < n do
      in.readUnsignedByte() match
        case 1             => utf8(i) = in.readUTF()
        case 3 | 4         => in.readInt()
        case 5 | 6         => in.readLong(); i += 1
        case 7 | 8 | 16 | 19 | 20 => in.readUnsignedShort()
        case 9             => in.readUnsignedShort(); in.readUnsignedShort()
        case 10 | 11       => in.readUnsignedShort(); refs(i) = in.readUnsignedShort()
        case 12            => nameAndType(i) = in.readUnsignedShort(); in.readUnsignedShort()
        case 15            => in.readUnsignedByte(); in.readUnsignedShort()
        case 17 | 18       => in.readInt()
        case t             => throw IllegalStateException(s"constant pool tag $t")
      i += 1
    in.readUnsignedShort(); in.readUnsignedShort(); in.readUnsignedShort()
    (0 until in.readUnsignedShort()).foreach(_ => in.readUnsignedShort())
    def skipAttributes(): Unit = (0 until in.readUnsignedShort()).foreach { _ => in.readUnsignedShort(); in.skipBytes(in.readInt()) }
    (0 until in.readUnsignedShort()).foreach { _ => in.skipBytes(6); skipAttributes() }
    val methods = (0 until in.readUnsignedShort()).flatMap { _ =>
      in.readUnsignedShort()
      val (name, desc) = (utf8(in.readUnsignedShort()), utf8(in.readUnsignedShort()))
      (0 until in.readUnsignedShort()).flatMap { _ =>
        val attr = utf8(in.readUnsignedShort())
        val len = in.readInt()
        if attr == "Code" then
          in.readUnsignedShort(); in.readUnsignedShort()
          val code = new Array[Byte](in.readInt())
          in.readFully(code)
          in.skipBytes(len - 8 - code.length)
          Some((name, desc) -> code)
        else { in.skipBytes(len); None }
      }
    }.toMap
    Bytecode(methods, ix => refs.get(ix).flatMap(nameAndType.get).flatMap(utf8.get))
