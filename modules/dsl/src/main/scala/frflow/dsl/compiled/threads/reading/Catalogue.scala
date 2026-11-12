package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Arm, Ctor, Decl, Draft, Param, Pattern, Term, Ty}
import scala.collection.mutable

/** The definitions the code read may mention beside its own (`core.threads.Support`), each made the first time
  * the reader writes its name: a cast, a global, a case of `obj`. A file holds those its definitions do mention
  * (`core.threads.Assemble`), so one made for code that turned out not to be read is not written.
  */
private[threads] final class Catalogue:
  private val castsMade = mutable.LinkedHashMap.empty[String, Decl.Definition]
  private val globalsMade = mutable.LinkedHashMap.empty[String, Decl.Definition]
  private val heldMade = mutable.LinkedHashMap.empty[String, Ctor]
  private val globalKinds = mutable.Map.empty[String, mutable.ListBuffer[String]]
  private val unreadSeen = mutable.ListBuffer.empty[Draft.Unread]

  /** What was not read, and why, in the order it was met. */
  def unread: List[Draft.Unread] = unreadSeen.toList
  def refused(what: String, why: String): Unit = unreadSeen += Draft.Unread(what, why)

  def casts: List[Decl.Definition] = castsMade.values.toList
  def globals: List[Decl.Definition] = globalsMade.values.toList
  def held: List[Ctor] = heldMade.values.toList

  private def cast(d: Decl.Definition): String = castsMade.getOrElseUpdate(d.name, d).name

  /** The case of `obj` for an object of the class read as `ty`: `O_<ty>`. */
  def obj(ty: String): String = heldMade.getOrElseUpdate(s"O_$ty", Catalogue.obj(ty)).name

  /** The case of `obj` for one object: `O_<owner>_<name>`. */
  def singleton(owner: String, name: String): String =
    heldMade.getOrElseUpdate(s"O_${owner}_$name", Ctor(s"O_${owner}_$name", Nil)).name

  /** A top-level value that is a handle to an object of the class `of`: the first of its class is `0`, the next
    * `1`, so that two are not the same object.
    */
  def global(name: String, of: String): String =
    val made = globalKinds.getOrElseUpdate(of, mutable.ListBuffer.empty)
    if !made.contains(name) then made += name
    globalsMade.getOrElseUpdate(name, Decl.Definition(name, Nil, Ty.Nat, Term.Ref(made.indexOf(name).toString))).name

  private def matching(on: String, pattern: Pattern, gives: Term, otherwise: Term): Term =
    Term.Match(Term.Ref(on), List(Arm(pattern, gives), Arm(Pattern.Wild, otherwise)))

  /** `cast_<ty>`: a `val` read as an object of the class read as `ty`. */
  def fromVal(ty: String): String = cast(Decl.Definition(s"cast_$ty", List(Param("v", Ty.Val)), Decl.M(Ty.Named(ty)),
    matching("v", Pattern.Ctor("VObj", List(Pattern.of(obj(ty), "x"))), Term.ret(Term.Ref("x")),
      Term.Ref("type_error"))))

  /** `cast_option_<ty>`: a `val` that may be null read as an object of the class read as `ty`, or none. */
  def fromNullable(ty: String): String =
    val some = Term.Bind("x", Term.of(fromVal(ty), Term.Ref("v")), Term.ret(Term.of("Some", Term.Ref("x"))))
    cast(Decl.Definition(s"cast_option_$ty", List(Param("v", Ty.option(Ty.Val))),
      Decl.M(Ty.option(Ty.Named(ty))), Term.Match(Term.Ref("v"), List(Arm(Pattern.of("Some", "v"), some),
        Arm(Pattern.of("None"), Term.ret(Term.Ref("None")))))))

  /** `cast_<ty>`: a value of the sum `sum` read as its case `ty`, held by the constructor `ctor`. */
  def fromSum(sum: String, ty: String, ctor: String): String =
    cast(Decl.Definition(s"cast_$ty", List(Param("s", Ty.Named(sum))), Decl.M(Ty.Named(ty)),
      matching("s", Pattern.of(ctor, "x"), Term.ret(Term.Ref("x")), Term.Ref("type_error"))))

  /** `cast_list`: a `val` read as a list. */
  def list: String = cast(Decl.Definition("cast_list", List(Param("v", Ty.Val)), Decl.M(Ty.list(Ty.Val)),
    matching("v", Pattern.of("VList", "xs"), Term.ret(Term.Ref("xs")), Term.Ref("type_error"))))

  /** `is_<name>`: whether a `val` is the object `O_<owner>_<name>`. */
  def is(owner: String, name: String): String =
    cast(Decl.Definition(s"is_$name", List(Param("v", Ty.Val)), Ty.Bool, matching("v",
      Pattern.Ctor("VObj", List(Pattern.of(singleton(owner, name)))), Term.Ref("true"), Term.Ref("false"))))

private[threads] object Catalogue:
  /** The case of `obj` that holds an object of the class read as `ty`. */
  def obj(ty: String): Ctor = Ctor(s"O_$ty", List(Param("x", Ty.Named(ty))))
