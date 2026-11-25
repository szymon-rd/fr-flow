package frflow.proof.rocq

import frflow.core.staged.{Arg, Handler, P}

/** A staged program as Rocq, over `FrFlow/Code/Staged.v`: one operation a line, what it gave named before `<~`. */
final class PrintStaged(values: PrintStagedValues):
  private def in(lines: List[String]): List[String] = lines.map("  " + _)

  /** `lines` in parentheses, where a program stands as an argument. */
  private def enclosed(lines: List[String]): List[String] = lines match
    case one :: Nil => List(s"($one)")
    case several    => ("(" + several.head) :: several.tail.init.map(" " + _) ::: List(" " + several.last + ")")

  /** `lines`, the last followed by `close`. */
  private def closed(lines: List[String], close: String): List[String] = lines.init :+ (lines.last + close)

  def apply(p: P): List[String] = p match
    case P.Give(v)                    => List(s"Staged.give ${values.value(v)}")
    case P.Bind(x, of, next)          => bound(x, apply(of)) ++ apply(next)
    case P.Let(x, v, next)            => s"let $x := ${values.value(v)} in" :: apply(next)
    case P.Op(name, args)             => operation(name, args)
    case P.Truth(v, yes, no)          => cases(values.value(v), List("VBool true" -> apply(yes),
      "VBool false" -> apply(no), "_" -> List("stuck \"a condition that gave no truth value\"")))
    case P.Parts(of, names, found, missed) => parts(apply(of), names, apply(found), apply(missed))
    case P.Share(x, shared, next)     => (s"let $x : D :=" :: in(apply(shared))) ++ ("in" :: apply(next))
    case P.Use(x)                     => List(x)
    case P.Stuck(why)                 => List(s"stuck \"${why.replace("\"", "\"\"")}\"")
    case P.Given(names, body)         => cases("args", List(names.mkString("[", "; ", "]") -> apply(body),
      "_" -> List("stuck \"a call given other than what the definition takes\"")))
    case P.Handle(body, handler, last) => handled(apply(body), handler, last.map(apply))

  private def bound(x: String, of: List[String]): List[String] = of match
    case one :: Nil => List(s"$x <~ $one ;;")
    case several    =>
      val wrapped = enclosed(several)
      (s"$x <~ ${wrapped.head}" :: wrapped.tail.init.map("  " + _)) :+ ("  " + wrapped.last + " ;;")

  private def cases(on: String, of: List[(String, List[String])]): List[String] =
    (s"match $on with" :: of.flatMap((pattern, body) => s"| $pattern =>" :: in(in(body)))) :+ "end"

  private def parts(of: List[String], names: List[String], found: List[String], missed: List[String]): List[String] =
    bound("parts", of) ++ cases("parts", List(s"Some ${names.mkString("[", "; ", "]")}" -> found,
      "Some _" -> List("stuck \"a pattern with more or fewer parts than the value\""), "None" -> missed))

  /** An operation applied: its simple arguments on its line, each program it is given on lines of its own. */
  private def operation(name: String, args: List[Arg]): List[String] =
    val (programs, simple) = args.partition(a => a.isInstanceOf[Arg.Prog] || a.isInstanceOf[Arg.Lazily])
    val head = (s"Staged.$name T" :: simple.map(values.simple)).mkString(" ")
    head :: programs.flatMap {
      case Arg.Prog(p)      => in(enclosed(apply(p)))
      case Arg.Lazily(each) => in(listed(each.map {
        case Left(v)  => List(s"inl ${values.value(v)}")
        case Right(q) => "inr" :: in(enclosed(apply(q)))
      }))
      case _                => Nil
    }

  private def listed(items: List[List[String]]): List[String] = items match
    case Nil => List("[]")
    case _   =>
      val separated = items.zipWithIndex.map((item, i) =>
        if i < items.size - 1 then item.init :+ (item.last + ";") else item)
      ("[" :: in(separated.flatten)) :+ "]"

  private def handled(body: List[String], handler: Option[Handler], last: Option[List[String]]): List[String] =
    val caught = handler.fold(List("None"))(h =>
      s"(Some (fun ${h.thrown} ${h.value} =>" :: closed(in(apply(h.body)), "))"))
    val finally_ = last.fold(List("None"))(l => "(Some" :: closed(in(enclosed(l)), ")"))
    "Staged.try_ T" :: in(enclosed(body)) ::: in(caught) ::: in(finally_)
