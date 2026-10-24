package rebac

import frflow.*

// ============================================================================
// The purpose: a check answers exactly what the tuples of its version give
// ============================================================================

val allowed = Param[(Query, Int) => Boolean]("allowed",
  "the service's answer to a check at a version (whether it allows the request)")

val checksExactly = Node.claim("ChecksExactly",
  "A check of whether a person has a relation to an object, at a version, answers yes exactly when the tuples stored at that version give it under the schema, within the resolution depth.",
  why = "The idea's lead paragraph (Q1), stated as one relation between what a client observes (the answer) and what the stored tuples entitle the person to (granted, fixed by Derivation). Stating it at a version makes the answer a function of the tuples a check reads (Q4); the depth bounds the derivation as OpenFGA's resolver does (Q3).",
  idea = "Checks"
)(forall((q: Term[Query], v: Term[Int]) => allowed(q, v) === granted(q, v)))

// ============================================================================
// The vocabulary: what a version holds, and what the tuples give
// ============================================================================

val versions = Node.definition("Versions",
  "An object's tuples at a version are those about it that the first v writes leave, applied in order: an added tuple once, a removed one gone.",
  why = "Each write and delete gets the next version, and a check reads one version (Q4): so a version's tuples are a prefix of the log replayed, and a later write never changes them."
)(stored := ((v: Term[Int], o: Term[Obj]) => tuplesAt(writes, v).filter(t => t.obj === o)))

val derivation = Node.definition("Derivation",
  "The tuples of a version give a person a relation on an object when, within the depth, a rule the schema gives that relation does: a tuple of the relation naming the person, or a userset the person is in; the relation it is implied by; or the relation inherited through a linked object.",
  why = "The schema's four kinds of rule (Q2), read one object at a time; a userset, an implied relation and a link each take a step, and what is given only beyond the depth is not given (Q3), as in OpenFGA."
)(granted := ((q: Term[Query], v: Term[Int]) => holds(levels, v, q.obj, q.rel, q.person)))

// ============================================================================
// The operations the check reads through: the store's index, and the schema's
// ============================================================================

val tuplesOf = Param[(Int, Obj) => List[RelTuple]]("tuplesOf",
  "the tuple store's answer to a read of one object's tuples at a version: the store keeps an index by object, as Zanzibar reads by object")
val rulesFor = Param[(String, String) => List[Rule]]("rulesFor",
  "the schema index's answer for a relation of a kind of object: the rules that give it")

val storeIndex = Node.assumption(tuplesOf)("StoreIndex",
  "A read of an object's tuples at a version returns exactly the tuples about it stored at that version, in the order they were added.",
  why = "The tuples live in the store, which keeps them by object and version; the check is proven from this promise, not from the store's code. The in-memory store (TupleStore) stands for a database here: its reads are checked against `storedOf` (this promise as code) on the examples and on generated logs of writes, and every read is checked to be about the object asked.",
  idea = "Versions and the cache"
)((v, o, ts) => ts === stored(v, o))
  .under(checksExactly)
  .checkedBy((v, o, ts) => ts.forall(t => t.obj === o))
  .examples(writes.bind(demoWrites))(
    expect(2, Obj("doc", "readme"), List(RelTuple(Obj("doc", "readme"), "parent", Subject.Link(Obj("folder", "eng")))),
      "the first two writes leave the readme's link to its folder; the folder's own tuple is about another object"),
    expect(5, Obj("group", "eng"), Nil, "ann was added to the group and removed again: nothing is left about it"),
    reject(1, Obj("doc", "readme"), List(RelTuple(Obj("doc", "readme"), "parent", Subject.Link(Obj("folder", "eng")))),
      "at version 1 only the folder's tuple was written: a read never shows a later write"))

/** The promise of StoreIndex as code: what the store's reads are checked against, and what Lean evaluates them by. */
val storedOf = define { (v: Term[Int], o: Term[Obj]) => stored(v, o) }

val schemaIndex = Node.contract(rulesFor)("SchemaIndex",
  "The schema index gives a relation of a kind of object exactly the rules the schema gives it, and none for a relation the schema does not name.",
  why = "Checks look rules up on every step; an index by kind and relation makes that cheap. Lean proves `rulesOf` meets this contract; the index that runs (SchemaIndex.scala, plain Scala) is checked against `rulesOf` on the examples and on generated schemas. The check is proven from the contract.",
  idea = "The schema"
)((kind, rel, rules) => rules === rulesOf(kind, rel))
  .under(checksExactly)
  .examples(schema.bind(demoSchema))(
    expect("doc", "viewer", List(Rule.Direct, Rule.Implied("editor"), Rule.Inherited("parent", "viewer")), "a document's viewers: its own tuples, its editors, and its folder's viewers"),
    expect("doc", "owner", Nil, "a relation the schema does not name has no rules"),
    reject("folder", "viewer", List(Rule.Direct, Rule.Implied("editor")), "a rule the schema does not give a relation is never added"))

// ============================================================================
// The check: proven of the code, which reads through the two indexes
// ============================================================================

/** The check's resolution: `holds`, step for step, reading an object's tuples through the store's index and a
  * relation's rules through the schema index, as the running service does.
  */
val resolve: Def[(List[Unit], Int, Obj, String, String) => Boolean] = define {
  (fuel: Term[List[Unit]], v: Term[Int], o: Term[Obj], r: Term[String], p: Term[String]) =>
    fuel.on[Nil.type](False).on[::[Unit]]((_, rest) =>
      rulesFor(o.kind, r).exists(rule =>
        rule.on[Rule.Direct.type](
              tuplesOf(v, o).exists(t => t.rel === r && t.subject
                .on[Subject.Person](id => id === p)
                .on[Subject.Members]((g, gr) => resolve(rest, v, g, gr, p))
                .on[Subject.Link](_ => False)))
            .on[Rule.Implied](by => resolve(rest, v, o, by, p))
            .on[Rule.Inherited]((link, via) =>
              tuplesOf(v, o).exists(t => t.rel === link && t.subject
                .on[Subject.Person](_ => False)
                .on[Subject.Members]((_, _) => False)
                .on[Subject.Link](parent => resolve(rest, v, parent, via, p))))))
}

/** A check: resolution from the object and relation asked, with the configured depth. */
val resolveCheck = define { (q: Term[Query], v: Term[Int]) => resolve(levels, v, q.obj, q.rel, q.person) }

val checkContract = Node.contract(allowed)("CheckContract",
  "A check at a version answers what resolving it gives: the rules of the relation asked, from the schema index, and the tuples of the objects they lead to, from the store's index at that version, step by step within the depth.",
  why = "How the service answers, stated as the resolution it runs: one object's tuples at a time, as Zanzibar reads, instead of the whole store. That this resolution gives exactly what the tuples of the version give (Derivation) is the root's split, proven by induction on the depth from the two indexes' promises.",
  idea = "Checks"
)((q, v, answer) => answer === resolve(levels, v, q.obj, q.rel, q.person))
  .under(checksExactly)
  .examples(schema.bind(demoSchema), levels.bind(demoLevels), writes.bind(demoWrites))(
    expect(Query(readme, "viewer", "ann"), 3, true, "at version 3 ann is in the eng group, whose members view the folder that holds the readme"),
    expect(Query(readme, "viewer", "ann"), 2, false, "at version 2 ann is not yet in the group"),
    expect(Query(readme, "viewer", "ann"), 5, false, "at version 5 she has left the group: the later write takes her access away"),
    expect(Query(readme, "viewer", "bob"), 4, true, "bob edits the readme, and an editor is a viewer"),
    reject(Query(readme, "editor", "ann"), 3, true, "viewing never implies editing"),
    reject(Query(readme, "viewer", "ann"), 3, false, "a derivation through a group and a folder is not turned away"))
