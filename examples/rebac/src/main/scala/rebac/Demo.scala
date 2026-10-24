package rebac

// The data the examples are decided with: a small schema, a log of writes, the default depth.

val docViewer = RelationDef("doc", "viewer", List(Rule.Direct, Rule.Implied("editor"), Rule.Inherited("parent", "viewer")))
val docEditor = RelationDef("doc", "editor", List(Rule.Direct))
val folderViewer = RelationDef("folder", "viewer", List(Rule.Direct))
val groupMember = RelationDef("group", "member", List(Rule.Direct))
/** The schema the examples are decided with. */
val demoSchema: List[RelationDef] = List(docViewer, docEditor, folderViewer, groupMember)

val readme = Obj("doc", "readme")
val eng = Obj("folder", "eng")
val engGroup = Obj("group", "eng")
/** Ann is in the eng group, whose members view the eng folder, which holds the readme; then she leaves the group. */
val demoWrites: List[Write] = List(
  Write.Add(RelTuple(eng, "viewer", Subject.Members(engGroup, "member"))),
  Write.Add(RelTuple(readme, "parent", Subject.Link(eng))),
  Write.Add(RelTuple(engGroup, "member", Subject.Person("ann"))),
  Write.Add(RelTuple(readme, "editor", Subject.Person("bob"))),
  Write.Remove(RelTuple(engGroup, "member", Subject.Person("ann"))))
/** The depth the examples are decided with: 4 steps, one more than their longest derivation (3: the readme's folder,
  * the folder's group, the group's member). Lean evaluates the examples by unfolding the derivation; at 25 steps that
  * exceeds its recursion limit, and at 6 the indexed resolution does.
  */
val demoLevels: List[Unit] = List.fill(4)(())
/** The depth the service runs with: OpenFGA's default. */
val serviceLevels: List[Unit] = List.fill(25)(())

