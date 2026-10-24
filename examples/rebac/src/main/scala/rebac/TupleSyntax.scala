package rebac

/** Tuples as clients write them: `doc:readme#viewer@user:ann` (a person), `folder:eng#viewer@group:eng#member` (a
  * userset), `doc:readme#parent@>folder:eng` (a link). Plain code: a malformed tuple is refused with the reason, so it
  * can never become a tuple; `show` writes what `parse` reads.
  */
object TupleSyntax:
  def parse(text: String): Either[String, RelTuple] =
    text.split("@", 2) match
      case Array(left, right) =>
        for
          (o, r) <- objectRelation(left)
          s      <- subject(right)
        yield RelTuple(o, r, s)
      case _ => Left(s"no subject: write object#relation@subject, as in doc:readme#viewer@user:ann")

  def show(t: RelTuple): String =
    def obj(o: Obj) = s"${o.kind}:${o.id}"
    val subject = t.subject match
      case Subject.Person(id)     => s"user:$id"
      case Subject.Members(o, r)  => s"${obj(o)}#$r"
      case Subject.Link(o)        => s">${obj(o)}"
    s"${obj(t.obj)}#${t.rel}@$subject"

  private def obj(s: String): Either[String, Obj] = s.split(":", 2) match
    case Array(k, i) if k.nonEmpty && i.nonEmpty && !i.contains('#') && !i.contains('@') => Right(Obj(k, i))
    case _ => Left(s"not an object: '$s' (write kind:id)")

  private def objectRelation(s: String): Either[String, (Obj, String)] = s.split("#", 2) match
    case Array(o, r) if r.nonEmpty => obj(o).map(_ -> r)
    case _                         => Left(s"no relation: '$s' (write kind:id#relation)")

  private def subject(s: String): Either[String, Subject] =
    if s.startsWith(">") then obj(s.drop(1)).map(Subject.Link(_))
    else s.split("#", 2) match
      case Array(o, r) if r.nonEmpty => obj(o).map(Subject.Members(_, r))
      case Array(_, _)               => Left(s"a userset names its relation: '$s' (write kind:id#relation)")
      case Array(p) if p.startsWith("user:") && p.length > 5 => Right(Subject.Person(p.drop(5)))
      case _ => Left(s"not a subject: '$s' (write user:id, kind:id#relation or >kind:id)")
