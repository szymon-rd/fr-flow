package frflow.ir

import frflow.json.Json
import frflow.json.Json.*

/** JSON encoding of the IR. The lifter embeds lifted expressions in the compiled
  * program as encoded strings, which are decoded when the model is built.
  */
object IrCodec:

  final class DecodeError(msg: String) extends RuntimeException(msg)

  private def fail(what: String, j: Json): Nothing = throw DecodeError(s"cannot decode $what from ${j.compact.take(200)}")

  private def tag(t: String, xs: Json*): Json = JArr(JStr(t) +: xs)
  private def s(x: String): Json = JStr(x)
  private def list[A](xs: List[A])(f: A => Json): Json = JArr(xs.map(f))

  // -- types ---------------------------------------------------------------

  def tpe(t: Type): Json = t match
    case Type.Bool          => s("Bool")
    case Type.Int           => s("Int")
    case Type.Str           => s("Str")
    case Type.Unit          => s("Unit")
    case Type.Named(n)      => tag("Named", s(n))
    case Type.ListOf(e)     => tag("List", tpe(e))
    case Type.SetOf(e)      => tag("Set", tpe(e))
    case Type.MapOf(k, v)   => tag("Map", tpe(k), tpe(v))
    case Type.OptionOf(e)   => tag("Option", tpe(e))
    case Type.TupleOf(es)   => tag("Tuple", list(es)(tpe))
    case Type.Fun(ps, r)    => tag("Fun", list(ps)(tpe), tpe(r))

  def readType(j: Json): Type = j match
    case JStr("Bool") => Type.Bool
    case JStr("Int")  => Type.Int
    case JStr("Str")  => Type.Str
    case JStr("Unit") => Type.Unit
    case JArr(Seq(JStr("Named"), JStr(n)))   => Type.Named(n)
    case JArr(Seq(JStr("List"), e))          => Type.ListOf(readType(e))
    case JArr(Seq(JStr("Set"), e))           => Type.SetOf(readType(e))
    case JArr(Seq(JStr("Map"), k, v))        => Type.MapOf(readType(k), readType(v))
    case JArr(Seq(JStr("Option"), e))        => Type.OptionOf(readType(e))
    case JArr(Seq(JStr("Tuple"), JArr(es)))  => Type.TupleOf(es.map(readType).toList)
    case JArr(Seq(JStr("Fun"), JArr(ps), r)) => Type.Fun(ps.map(readType).toList, readType(r))
    case _                                   => fail("type", j)

  // -- expressions ---------------------------------------------------------

  private def param(p: Param): Json = JArr(Seq(s(p.name), tpe(p.tpe)))
  private def readParam(j: Json): Param = j match
    case JArr(Seq(JStr(n), t)) => Param(n, readType(t))
    case _                     => fail("parameter", j)

  def pattern(p: Pattern): Json = p match
    case Pattern.Wild          => s("_")
    case Pattern.Bind(n, q)    => tag("Bind", s(n), pattern(q))
    case Pattern.Ctor(c, args) => tag("Ctor", s(c), list(args)(pattern))
    case Pattern.Lit(e)        => tag("Lit", expr(e))

  def readPattern(j: Json): Pattern = j match
    case JStr("_")                                   => Pattern.Wild
    case JArr(Seq(JStr("Bind"), JStr(n), q))         => Pattern.Bind(n, readPattern(q))
    case JArr(Seq(JStr("Ctor"), JStr(c), JArr(as)))  => Pattern.Ctor(c, as.map(readPattern).toList)
    case JArr(Seq(JStr("Lit"), e))                   => Pattern.Lit(readExpr(e))
    case _                                           => fail("pattern", j)

  def expr(e: Expr): Json = e match
    case Expr.Var(n)                 => tag("Var", s(n))
    case Expr.BoolLit(b)             => tag("Bool", JBool(b))
    case Expr.IntLit(v)              => tag("Int", s(v.toString))
    case Expr.StrLit(v)              => tag("Str", s(v))
    case Expr.UnitLit                => tag("Unit")
    case Expr.Field(t, f)            => tag("Field", expr(t), s(f))
    case Expr.Construct(c, as)       => tag("New", s(c), list(as)(expr))
    case Expr.With(t, us)            => tag("With", expr(t), list(us)((f, x) => JArr(Seq(s(f), expr(x)))))
    case Expr.Call(f, as, m)         => tag("Call", s(f), list(as)(expr), JBool(m))
    case Expr.Ref(n)                 => tag("Ref", s(n))
    case Expr.PrimOp(op, as, t)      => tag("Prim", s(op.toString), list(as)(expr), t.fold(JNull)(tpe))
    case Expr.Lam(ps, b)             => tag("Lam", list(ps)(param), expr(b))
    case Expr.App(f, as)             => tag("App", expr(f), list(as)(expr))
    case Expr.If(c, t, el)           => tag("If", expr(c), expr(t), expr(el))
    case Expr.Match(sc, cs)          => tag("Match", expr(sc), list(cs)(c => JArr(Seq(pattern(c.pat), expr(c.body)))))
    case Expr.Let(n, t, v, b)        => tag("Let", s(n), tpe(t), expr(v), expr(b))
    case Expr.Quant(q, ps, b)        => tag("Quant", s(q.toString), list(ps)(param), expr(b))

  def readExpr(j: Json): Expr = j match
    case JArr(JStr(t) +: xs) =>
      (t, xs) match
        case ("Var", Seq(JStr(n)))                     => Expr.Var(n)
        case ("Bool", Seq(JBool(b)))                   => Expr.BoolLit(b)
        case ("Int", Seq(JStr(v)))                     => Expr.IntLit(BigInt(v))
        case ("Str", Seq(JStr(v)))                     => Expr.StrLit(v)
        case ("Unit", Seq())                           => Expr.UnitLit
        case ("Field", Seq(x, JStr(f)))                => Expr.Field(readExpr(x), f)
        case ("New", Seq(JStr(c), JArr(as)))           => Expr.Construct(c, as.map(readExpr).toList)
        case ("With", Seq(x, JArr(us))) =>
          Expr.With(readExpr(x), us.map {
            case JArr(Seq(JStr(f), v)) => f -> readExpr(v)
            case other                 => fail("update", other)
          }.toList)
        case ("Call", Seq(JStr(f), JArr(as), JBool(m))) => Expr.Call(f, as.map(readExpr).toList, m)
        case ("Ref", Seq(JStr(n)))                     => Expr.Ref(n)
        case ("Prim", Seq(JStr(op), JArr(as), t)) =>
          Expr.PrimOp(Prim.valueOf(op), as.map(readExpr).toList, if t == JNull then None else Some(readType(t)))
        case ("Lam", Seq(JArr(ps), b))                 => Expr.Lam(ps.map(readParam).toList, readExpr(b))
        case ("App", Seq(f, JArr(as)))                 => Expr.App(readExpr(f), as.map(readExpr).toList)
        case ("If", Seq(c, a, b))                      => Expr.If(readExpr(c), readExpr(a), readExpr(b))
        case ("Match", Seq(sc, JArr(cs))) =>
          Expr.Match(readExpr(sc), cs.map {
            case JArr(Seq(p, b)) => Case(readPattern(p), readExpr(b))
            case other           => fail("case", other)
          }.toList)
        case ("Let", Seq(JStr(n), t, v, b))            => Expr.Let(n, readType(t), readExpr(v), readExpr(b))
        case ("Quant", Seq(JStr(q), JArr(ps), b))      => Expr.Quant(Quantifier.valueOf(q), ps.map(readParam).toList, readExpr(b))
        case _                                         => fail("expression", j)
    case _ => fail("expression", j)

  // -- definitions ---------------------------------------------------------

  private def field(f: FieldDef): Json = JArr(Seq(s(f.name), tpe(f.tpe), s(f.doc)))
  private def readField(j: Json): FieldDef = j match
    case JArr(Seq(JStr(n), t, JStr(d))) => FieldDef(n, readType(t), d)
    case _                              => fail("field", j)

  def adt(a: AdtDef): Json =
    val shape = a.shape match
      case AdtShape.Product(fs) => tag("Product", list(fs)(field))
      case AdtShape.Sum(cs)     => tag("Sum", list(cs)(c => JArr(Seq(s(c.name), list(c.fields)(field), s(c.doc)))))
    obj("name" -> s(a.name), "scala" -> s(a.scalaName), "shape" -> shape, "doc" -> s(a.doc), "source" -> s(a.source))

  def readAdt(j: Json): AdtDef =
    val shape = j("shape") match
      case Some(JArr(Seq(JStr("Product"), JArr(fs)))) => AdtShape.Product(fs.map(readField).toList)
      case Some(JArr(Seq(JStr("Sum"), JArr(cs)))) =>
        AdtShape.Sum(cs.map {
          case JArr(Seq(JStr(n), JArr(fs), JStr(d))) => CtorDef(n, fs.map(readField).toList, d)
          case other                                 => fail("constructor", other)
        }.toList)
      case other => fail("ADT shape", other.getOrElse(JNull))
    AdtDef(str(j, "name"), str(j, "scala"), shape, str(j, "doc"), str(j, "source"))

  def fun(f: FunDef): Json =
    obj(
      "name" -> s(f.name), "scala" -> s(f.scalaName), "params" -> list(f.params)(param), "result" -> tpe(f.result),
      "body" -> expr(f.body), "doc" -> s(f.doc), "source" -> s(f.source)
    )

  def readFun(j: Json): FunDef =
    FunDef(
      str(j, "name"), str(j, "scala"), j("params").map(_.arr).getOrElse(Nil).map(readParam).toList,
      readType(j("result").getOrElse(fail("result", j))), readExpr(j("body").getOrElse(fail("body", j))),
      str(j, "doc"), str(j, "source")
    )

  def defs(d: Defs): Json =
    obj("adts" -> JArr(d.adts.values.toSeq.sortBy(_.name).map(adt)), "funs" -> JArr(d.funs.values.toSeq.sortBy(_.name).map(fun)))

  def readDefs(j: Json): Defs =
    Defs(
      j("adts").map(_.arr).getOrElse(Nil).map(readAdt).map(a => a.name -> a).toMap,
      j("funs").map(_.arr).getOrElse(Nil).map(readFun).map(f => f.name -> f).toMap
    )

  def lifted(l: Lifted): Json =
    obj(
      "params" -> list(l.params)(param), "result" -> tpe(l.result), "body" -> expr(l.body),
      "source" -> s(l.source), "position" -> s(l.position)
    )

  def readLifted(j: Json): Lifted =
    Lifted(
      j("params").map(_.arr).getOrElse(Nil).map(readParam).toList, readType(j("result").getOrElse(fail("result", j))),
      readExpr(j("body").getOrElse(fail("body", j))), str(j, "source"), str(j, "position")
    )

  def result(r: LiftResult): Json =
    obj("lifted" -> r.lifted.fold(JNull)(lifted), "type" -> tpe(r.tpe), "defs" -> defs(r.defs))

  def readResult(j: Json): LiftResult =
    LiftResult(
      j("lifted").filter(_ != JNull).map(readLifted),
      readType(j("type").getOrElse(fail("type", j))),
      j("defs").map(readDefs).getOrElse(Defs.empty)
    )

  /** Encodes a lift result as string chunks that fit in JVM string constants. */
  def encodeChunks(r: LiftResult): List[String] = result(r).compact.grouped(16000).toList

  def decodeChunks(chunks: Seq[String]): LiftResult = readResult(Json.parse(chunks.mkString))

  private def str(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")
