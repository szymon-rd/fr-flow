package frflow

import java.lang.invoke.SerializedLambda
import scala.util.Try

/** What the JVM keeps of a Scala lambda: its parameters' names, and the class (file or object) it was written in.
  * Scala compiles a lambda to a serializable method reference, whose method keeps the parameters' names.
  */
private[frflow] object Lambdas:
  private def serialized(f: AnyRef): Option[SerializedLambda] = Try {
    val m = f.getClass.getDeclaredMethod("writeReplace")
    m.setAccessible(true)
    m.invoke(f).asInstanceOf[SerializedLambda]
  }.toOption

  private def load(internal: String): Class[?] = Class.forName(internal.replace('/', '.'), false, getClass.getClassLoader)

  /** The names of the lambda's parameters, without the values it captures; empty when the JVM kept none. */
  def params(f: AnyRef): List[String] =
    serialized(f).flatMap { sl =>
      Try {
        val m = load(sl.getImplClass).getDeclaredMethods.find(_.getName == sl.getImplMethodName).get
        // An instance method's receiver is captured too, but is not one of its parameters.
        val receiver = if java.lang.reflect.Modifier.isStatic(m.getModifiers) then 0 else 1
        val ps = m.getParameters.toList.drop(sl.getCapturedArgCount - receiver)
        if ps.forall(_.isNamePresent) then ps.map(_.getName) else Nil
      }.toOption
    }.getOrElse(Nil)

  /** The values the lambda captures, each with the name the program gave it (`t` of a `val t` in an enclosing lambda);
    * the receiver of an instance method is not one of them.
    */
  def captured(f: AnyRef): List[(String, Any)] =
    serialized(f).flatMap { sl =>
      Try {
        val m = load(sl.getImplClass).getDeclaredMethods.find(_.getName == sl.getImplMethodName).get
        val receiver = if java.lang.reflect.Modifier.isStatic(m.getModifiers) then 0 else 1
        val names = m.getParameters.toList.take(sl.getCapturedArgCount - receiver)
          .map(p => if p.isNamePresent then p.getName.replaceAll("\\$\\d+$", "") else "x")
        names.zip((receiver until sl.getCapturedArgCount).map(sl.getCapturedArg).toList)
      }.toOption
    }.getOrElse(Nil)

  /** The name of the val holding `x`, in the file or object where the lambda `f` was written: `name`, or `Object.name`. */
  def valName(x: AnyRef, f: AnyRef): Option[String] =
    serialized(f).flatMap(sl => Try(load(sl.getCapturingClass)).toOption).flatMap { c =>
      Try(c.getField("MODULE$").get(null)).toOption.flatMap { holder =>
        c.getDeclaredFields.find { fl =>
          fl.setAccessible(true)
          Try(fl.get(holder)).toOption.exists(_.asInstanceOf[AnyRef] eq x)
        }.map { fl =>
          val n = Names.ident(fl.getName.replaceAll("\\$lzy\\d+$", ""))
          val owner = LeanType.qualified(c)
          if owner.isEmpty then n else s"$owner.$n"
        }
      }
    }
