package frflow.dsl.lifted

import frflow.dsl.term.{Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** The operations of Scala's immutable `List` and `Option` lifted code calls, each the term language's operation of
  * the same name and value (`forall`, `exists`, `filter`, `find`, `map`, `flatMap`, `contains`, `isEmpty`,
  * `nonEmpty`, `foldLeft`, `++`, `:+`, `::`; an option's `forall`, `exists`, `map`, `fold`, `getOrElse`, `contains`,
  * `isDefined`, `isEmpty`, `nonEmpty`). No other is read: `head`, `get` and `apply` are not total.
  */
private[lifted] trait ReadCollections extends Reading:
  this: Reader =>
  import q.reflect.*

  def list(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    elementOf(c.on.tpe, ListClass).flatMap(elem => joined(c).orElse(elem.asType match
      case '[a] => asked[a](c).orElse(mapped[a](c))))

  /** Lists joined, each side read at the list the whole is (`b :: Nil` is a list of `b`'s type). */
  private def joined(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    elementOf(c.own, ListClass).map(_.asType).flatMap { case '[b] =>
      (c.name, c.args) match
        case ("++" | ":::", List(ys)) if c.name == "++" =>
          Some('{ TermSyntax.++(${ readAs[List[b]](c.on) })(${ readAs[List[b]](ys) }) })
        case (":+", List(x))          => Some('{ TermSyntax.:+(${ readAs[List[b]](c.on) })(${ readAs[b](x) }) })
        case ("::", List(x))          => Some('{ LiftOps.cons[b](${ readAs[b](x) }, ${ readAs[List[b]](c.on) }) })
        case _                        => None
    }

  private def asked[A: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val (xs, a) = (readAs[List[A]](c.on), spec[A](c.on))
    (c.name, c.args) match
      case ("forall", List(p))   => Some('{ LiftOps.all[A]($xs, ${ hint(p) })(${ function[A, Boolean](p) })(using $a) })
      case ("exists", List(p))   => Some('{ LiftOps.any[A]($xs, ${ hint(p) })(${ function[A, Boolean](p) })(using $a) })
      case ("filter", List(p))   =>
        Some('{ LiftOps.filter[A]($xs, ${ hint(p) })(${ function[A, Boolean](p) })(using $a) })
      case ("find", List(p))     => Some('{ LiftOps.find[A]($xs, ${ hint(p) })(${ function[A, Boolean](p) })(using $a) })
      case ("contains", List(x)) => Some('{ LiftOps.contains[A]($xs, ${ readAs[A](x) }) })
      case ("isEmpty", Nil)      => Some('{ LiftOps.isEmpty[A]($xs) })
      case ("nonEmpty", Nil)     => Some('{ TermSyntax.unary_!(LiftOps.isEmpty[A]($xs)) })
      case _                     => None

  private def mapped[A: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val (xs, a) = (readAs[List[A]](c.on), spec[A](c.on))
    (c.name, c.args, elementOf(c.own, ListClass).map(_.asType), c.own.asType) match
      case ("map", List(f), Some('[b]), _)     =>
        Some('{ LiftOps.map[A, b]($xs, ${ hint(f) })(${ function[A, b](f) })(using $a, ${ spec[b](f) }) })
      case ("flatMap", List(f), Some('[b]), _) =>
        Some('{ LiftOps.flatMap[A, b]($xs, ${ hint(f) })(${ function[A, List[b]](f) })(using $a, ${ spec[b](f) }) })
      case ("foldLeft", List(z, f), _, '[b])   =>
        val names = hints(f).padTo(2, "x")
        Some('{ Terms.foldLeft[A, b]($xs, ${ readAs[b](z) }, (${ Expr(names(0)) }, ${ Expr(names(1)) }))(
          ${ function2[b, A, b](f) })(using $a) })
      case _                                   => None

  def option(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    elementOf(c.on.tpe, OptionClass).map(_.asType).flatMap { case '[a] => held[a](c).orElse(folded[a](c)) }

  private def held[A: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val (o, a) = (readAs[Option[A]](c.on), spec[A](c.on))
    (c.name, c.args) match
      case ("forall", List(p))            =>
        Some('{ LiftOps.optionAll[A]($o, ${ hint(p) })(${ function[A, Boolean](p) })(using $a) })
      case ("exists", List(p))            =>
        Some('{ LiftOps.optionAny[A]($o, ${ hint(p) })(${ function[A, Boolean](p) })(using $a) })
      case ("isDefined" | "nonEmpty", Nil) => Some('{ TermSyntax.isDefined[A]($o) })
      case ("isEmpty", Nil)               => Some('{ LiftOps.isNone[A]($o)(using $a) })
      case ("contains", List(x))          => Some('{ LiftOps.optionContains[A]($o, ${ readAs[A](x) })(using $a) })
      case ("getOrElse", List(d))         => Some('{ LiftOps.orElse[A]($o, ${ readAs[A](d) }) })
      case _                              => None

  private def folded[A: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val (o, a) = (readAs[Option[A]](c.on), spec[A](c.on))
    (c.name, c.args, elementOf(c.own, OptionClass).map(_.asType), c.own.asType) match
      case ("map", List(f), Some('[b]), _) =>
        Some('{ LiftOps.optionMap[A, b]($o, ${ hint(f) })(${ function[A, b](f) })(using $a, ${ spec[b](f) }) })
      case ("fold", List(z, f), _, '[r])   =>
        Some('{ Terms.foldOption[A, r]($o, ${ readAs[r](z) }, ${ hint(f) })(${ function[A, r](f) })(using $a) })
      case _                               => None

  /** A map's value at a key, a set's member, a pair's side. Maps and sets are not iterated. */
  def keyed(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    (argsOf(c.on.tpe, MapClass).map(_.asType), argsOf(c.on.tpe, SetClass).map(_.asType),
      argsOf(c.on.tpe, PairClass).map(_.asType)) match
      case (List('[k], '[v]), _, _) => map[k, v](c)
      case (_, List('[a]), _)       => set[a](c)
      case (_, _, List('[a], '[b])) => side[a, b](c)
      case _                        => None

  private def map[K: Type, V: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val (m, v) = (readAs[Map[K, V]](c.on), spec[V](c.on))
    (c.name, c.args) match
      case ("get", List(k))          => Some('{ TermSyntax.get[K, V]($m)(${ readAs[K](k) })(using $v) })
      case ("contains", List(k))     => Some('{ LiftOps.hasKey[K, V]($m, ${ readAs[K](k) })(using $v) })
      case ("getOrElse", List(k, d)) => Some('{ LiftOps.valueOr[K, V]($m, ${ readAs[K](k) }, ${ readAs[V](d) }) })
      case ("updated", List(k, x))   => Some('{ LiftOps.put[K, V]($m, ${ readAs[K](k) }, ${ readAs[V](x) }) })
      case _                         => None

  private def set[A: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val s = readAs[Set[A]](c.on)
    (c.name, c.args) match
      case ("contains" | "apply", List(x)) => Some('{ LiftOps.member[A]($s, ${ readAs[A](x) }) })
      case ("+" | "incl", List(x))         => Some('{ TermSyntax.incl[A]($s)(${ readAs[A](x) }) })
      case ("++" | "union", List(t))       => Some('{ TermSyntax.union[A]($s)(${ readAs[Set[A]](t) }) })
      case _                               => None

  private def side[A: Type, B: Type](c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    lazy val p = readAs[(A, B)](c.on)
    (c.name, c.args) match
      case ("_1", Nil) => Some('{ TermSyntax._1[A, B]($p)(using ${ spec[A](c.on) }) })
      case ("_2", Nil) => Some('{ TermSyntax._2[A, B]($p)(using ${ spec[B](c.on) }) })
      case _           => None

  private def hint(f: Term)(using Quotes): Expr[String] = Expr(hints(f).headOption.getOrElse("x"))
