package rebac

import frflow.*

// ============================================================================
// The domain: objects, subjects, relationship tuples, the schema, the write log
// ============================================================================

/** An object of the system, of a kind the schema names: `doc:readme`, `folder:eng`, `group:admins`. */
final case class Obj(kind: String, id: String)
object Obj extends Data[Obj]

/** Who a tuple gives a relation to. */
enum Subject:
  /** One person: `user:ann`. */
  case Person(id: String)
  /** Everyone who has a relation on an object: `group:eng#member`. */
  case Members(obj: Obj, rel: String)
  /** An object itself, the far end of a link: `folder:eng` in `doc:readme#parent@folder:eng`. */
  case Link(obj: Obj)
object Subject extends Data[Subject]

/** A relationship tuple: the subject has the relation on the object (`doc:readme#viewer@user:ann`). */
final case class RelTuple(obj: Obj, rel: String, subject: Subject)
object RelTuple extends Data[RelTuple]

/** How the schema gives a relation. */
enum Rule:
  /** By the relation's own tuples. */
  case Direct
  /** To whoever has another relation on the same object: an editor is a viewer. */
  case Implied(by: String)
  /** To whoever has `rel` on an object the `link` relation points to: a document's viewers include its folder's. */
  case Inherited(link: String, rel: String)
object Rule extends Data[Rule]

/** One relation of one kind of object, and the rules that give it. */
final case class RelationDef(kind: String, rel: String, rules: List[Rule])
object RelationDef extends Data[RelationDef]

/** A check: does the person have the relation on the object? */
final case class Query(obj: Obj, rel: String, person: String)
object Query extends Data[Query]

/** A check at a version: what a client sends, and what the cache keeps answers by. */
final case class Ask(query: Query, at: Int)
object Ask extends Data[Ask]

/** A change to the stored tuples. Each gets the next version: the log's length after it. */
enum Write:
  case Add(t: RelTuple)
  case Remove(t: RelTuple)
object Write extends Data[Write]

val schema = Param[List[RelationDef]]("schema", "the schema in force: for each kind of object, its relations and the rules that give each")
val levels = Param[List[Unit]]("levels",
  "the resolution depth, one entry per step a check may take (a userset, an implied relation or a link is a step), as configured: 25 entries in production, as OpenFGA's default")
val writes = Param[List[Write]]("writes", "every write and delete of a tuple, in order: version v is what the first v of them leave")

// ============================================================================
// The vocabulary the purpose is stated in, fixed by the definitions Versions and Derivation (Checks.scala)
// ============================================================================

val stored = Param[(Int, Obj) => List[RelTuple]]("stored",
  "the tuples about an object stored at a version: what the writes up to that version leave about it")
val granted = Param[(Query, Int) => Boolean]("granted",
  "whether the tuples stored at the version give the person the relation on the object under the schema, within the depth")

/** The rules the schema gives a relation of a kind of object; none if the schema does not name it. */
val rulesOf = define { (kind: Term[String], rel: Term[String]) =>
  schema.find(d => d.kind === kind && d.rel === rel).fold(List.empty[Rule])(d => d.rules)
}

/** The tuples after one more write: an added tuple once, a removed one gone. */
val applyWrite = define { (ts: Term[List[RelTuple]], w: Term[Write]) =>
  w.on[Write.Add](t => ts.contains(t).fold(ts, ts ++ List(t)))
   .on[Write.Remove](t => ts.filterNot(x => x === t))
}
/** The tuples the first `v` writes leave, applied in order. */
val tuplesAt = define { (ws: Term[List[Write]], v: Term[Int]) =>
  ws.take(v).foldLeft(Nil: Term[List[RelTuple]])((ts, w) => applyWrite(ts, w))
}

/** Whether the tuples stored at version `v` give the person the relation on the object in at most as many steps as
  * `fuel` has entries: a step is one rule of the relation (its own tuples, an implied relation, a link), and a userset
  * or a link continues on the next step with the rest of the fuel. It reads an object's tuples (`stored`) and a
  * relation's rules (`rulesOf`), one object at a time, as the service's resolution does through its indexes.
  */
val holds: Def[(List[Unit], Int, Obj, String, String) => Boolean] = define {
  (fuel: Term[List[Unit]], v: Term[Int], o: Term[Obj], r: Term[String], p: Term[String]) =>
    fuel.on[Nil.type](False).on[::[Unit]]((_, rest) =>
      rulesOf(o.kind, r).exists(rule =>
        rule.on[Rule.Direct.type](
              stored(v, o).exists(t => t.rel === r && t.subject
                .on[Subject.Person](id => id === p)
                .on[Subject.Members]((g, gr) => holds(rest, v, g, gr, p))
                .on[Subject.Link](_ => False)))
            .on[Rule.Implied](by => holds(rest, v, o, by, p))
            .on[Rule.Inherited]((link, via) =>
              stored(v, o).exists(t => t.rel === link && t.subject
                .on[Subject.Person](_ => False)
                .on[Subject.Members]((_, _) => False)
                .on[Subject.Link](parent => holds(rest, v, parent, via, p))))))
}
