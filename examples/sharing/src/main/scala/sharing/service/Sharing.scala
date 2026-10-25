package sharing.service

import frflow.*
import sharing.*
import sharing.domain.*

/** The sharing rules: what a person can do with a document, and how sharing and moving change the library. Each
  * method is a function of the library; the effects (keeping the library, answering requests) live in `sharing.http`.
  */
trait Sharing:
  /** A person's access to a document: edit, view, or none. */
  def access(library: Library, person: PersonId, doc: DocumentId): Option[Level]
  def canView(library: Library, person: PersonId, doc: DocumentId): Boolean
  def canEdit(library: Library, person: PersonId, doc: DocumentId): Boolean
  /** The library after `by` shares `what` with `withWhom` at `level`. */
  def share(library: Library, by: PersonId, what: Target, withWhom: Grantee, level: Level): Library
  /** The library after `by` unshares `what` from `withWhom`. */
  def unshare(library: Library, by: PersonId, what: Target, withWhom: Grantee): Library
  /** The library after `by` moves `doc` into a folder, or out of every folder (`None`). */
  def move(library: Library, by: PersonId, doc: DocumentId, into: Option[FolderId]): Library

/** Sharing's operations: for each method, its contract and its code (a `define`, proven in Lean to meet it). */
object Sharing:
  import Demo.*

  val access = Param[(Library, PersonId, DocumentId) => Option[Level]]("access", "a person's access to a document, as the service works it out")
  val canView = Param[(Library, PersonId, DocumentId) => Boolean]("canView", "the service's answer to whether a person can view a document")
  val canEdit = Param[(Library, PersonId, DocumentId) => Boolean]("canEdit", "the service's answer to whether a person can edit a document")
  val share = Param[(Library, PersonId, Target, Grantee, Level) => Library]("share", "the library after someone asks to share a document or folder")
  val unshare = Param[(Library, PersonId, Target, Grantee) => Library]("unshare", "the library after someone asks to unshare a document or folder")
  val move = Param[(Library, PersonId, DocumentId, Option[FolderId]) => Library]("move", "the library after someone asks to move a document")

  // ---------------------------------------------------------------------------
  // access: worked out from the person's teams and the document's folders
  // ---------------------------------------------------------------------------

  /** Who a share must be with to reach the person: the person, or one of the teams they are in. */
  val granteesOf = define { (lib: Term[Library], p: Term[PersonId]) =>
    Grantee[Grantee.Person](p) :: lib.teams.filter(t => t.members.contains(p)).map(t => Grantee[Grantee.Team](t.id))
  }
  /** What a share must be of to cover the document: the document, or one of the folders around it. */
  val placesOf = define { (lib: Term[Library], d: Term[DocumentId]) =>
    Target[Target.Doc](d) :: lib.documents.filter(doc => doc.id === d).flatMap(doc => doc.folders.map(f => Target[Target.InFolder](f)))
  }
  /** The strongest level among some shares: edit if one is an edit share, view if there is any, none otherwise. */
  val strongest = define { (ss: Term[List[Share]]) =>
    ss.exists(s => s.level === Level.Edit).fold(some(Level.Edit: Term[Level]), ss.isEmpty.fold(none[Level], some(Level.View: Term[Level])))
  }

  val accessContract = Node.contract(access)("AccessContract",
    "A person's access to a document is worked out from their teams and the document's folders: among the shares with them or one of their teams, of the document or one of the folders around it, it is edit if one is an edit share, view if there is any, and none otherwise.",
    why = "This is how the service finds the shares that matter without asking every share whether it reaches the person and covers the document: it lists who a share must be with and what it must be of, once each. That this finds exactly the shares the meaning names (Reach, Cover) is what the purpose's proof shows.",
    idea = "Who can see and change what"
  )((lib, p, d, result) => result === strongest(lib.shares.filter(s => granteesOf(lib, p).contains(s.withWhom) && placesOf(lib, d).contains(s.what))))
    .under(accessFollowsShares)
    .examples()(
      expect(library, bob, q3Report, Some(Level.View), "Bob's team may view the reports folder, which the Q3 report is in"),
      expect(library, ann, q3Report, Some(Level.Edit), "Ann may edit the reports folder"),
      expect(library, cat, plan, None, "nothing is shared with Cat"),
      reject(library, bob, plan, Some(Level.View), "nothing shares the plan with Bob or his team"),
      reject(library, ann, plan, Some(Level.View), "Ann's share of the plan is an edit share: her access is edit"))

  /** Access, worked out: the shares with the person or one of their teams, of the document or a folder around it; the
    * strongest of them.
    */
  val accessCode = define { (lib: Term[Library], p: Term[PersonId], d: Term[DocumentId]) =>
    val (grantees, places) = (granteesOf(lib, p), placesOf(lib, d))
    strongest(lib.shares.filter(s => grantees.contains(s.withWhom) && places.contains(s.what)))
  }

  // ---------------------------------------------------------------------------
  // canView, canEdit: what the access allows
  // ---------------------------------------------------------------------------

  val canViewContract = Node.contract(canView)("CanViewContract",
    "A person can view a document exactly when they have some access to it.",
    why = "Viewing needs a share of any level, and editing includes viewing (Q1).",
    idea = "Who can see and change what"
  )((lib, p, d, result) => result === access(lib, p, d).isDefined)
    .under(accessFollowsShares)
    .examples()(
      expect(library, bob, q3Report, true, "Bob's team may view the reports folder"),
      expect(library, cat, q3Report, false, "nothing is shared with Cat"),
      reject(library, cat, plan, true, "Cat has no access to the plan"))

  val canViewCode = define { (lib: Term[Library], p: Term[PersonId], d: Term[DocumentId]) => access(lib, p, d).isDefined }

  val canEditContract = Node.contract(canEdit)("CanEditContract",
    "A person can edit a document exactly when their access to it is edit.",
    why = "Only an edit share lets someone change a document (Q1).",
    idea = "Who can see and change what"
  )((lib, p, d, result) => result === (access(lib, p, d) === some(Level.Edit: Term[Level])))
    .under(accessFollowsShares)
    .examples()(
      expect(library, ann, q3Report, true, "Ann may edit the reports folder, around the Q3 report"),
      expect(library, bob, q3Report, false, "Bob's team may only view it"),
      reject(library, bob, q3Report, true, "a view share never lets anyone edit"))

  val canEditCode = define { (lib: Term[Library], p: Term[PersonId], d: Term[DocumentId]) =>
    access(lib, p, d) === some(Level.Edit: Term[Level])
  }

  // ---------------------------------------------------------------------------
  // share, unshare, move: changes, made only by someone who may edit what they change
  // ---------------------------------------------------------------------------

  /** The shares, less any of `what` with `withWhom`. */
  val sharesWithout = define { (ss: Term[List[Share]], what: Term[Target], withWhom: Term[Grantee]) =>
    ss.filterNot(s => s.what === what && s.withWhom === withWhom)
  }

  val shareContract = Node.contract(share)("ShareContract",
    "Someone who may edit a document or folder shares it with a person or a team at a level: the new share takes the place of any earlier share of it with them. When anyone else asks, nothing changes.",
    why = "Anyone who can edit a document can share it (Q2), and a person or team has one share of a thing at a time, so sharing again changes the level rather than adding a second share.",
    idea = "Who can see and change what"
  )((lib, by, what, withWhom, level, result) =>
    result === mayEdit(lib, by, what).fold(
      lib.copy((shares = Share(what, withWhom, level) :: sharesWithout(lib.shares, what, withWhom))),
      lib))
    .under(accessFollowsShares)
    .examples()(
      expect(library, ann, Target.Doc(plan), Grantee.Person(bob), Level.View,
        library.copy(shares = Share(Target.Doc(plan), Grantee.Person(bob), Level.View) :: library.shares),
        "Ann may edit the plan, so she shares it with Bob"),
      expect(library, bob, Target.Doc(plan), Grantee.Person(bob), Level.Edit, library,
        "Bob may not edit the plan: his request changes nothing"),
      reject(library, bob, Target.InFolder(reports), Grantee.Person(cat), Level.View,
        library.copy(shares = Share(Target.InFolder(reports), Grantee.Person(cat), Level.View) :: library.shares),
        "Bob may only view the reports folder, so he cannot share it"))

  val shareCode = define { (lib: Term[Library], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee], level: Term[Level]) =>
    mayEdit(lib, by, what).fold(lib.copy((shares = Share(what, withWhom, level) :: sharesWithout(lib.shares, what, withWhom))), lib)
  }

  val unshareContract = Node.contract(unshare)("UnshareContract",
    "Someone who may edit a document or folder unshares it from a person or a team: their share of it goes. When anyone else asks, nothing changes.",
    why = "Unsharing is changing who a document is shared with, which only someone who may edit it does (Q2).",
    idea = "Who can see and change what"
  )((lib, by, what, withWhom, result) =>
    result === mayEdit(lib, by, what).fold(lib.copy((shares = sharesWithout(lib.shares, what, withWhom))), lib))
    .under(accessFollowsShares)
    .examples()(
      expect(library, ann, Target.InFolder(reports), Grantee.Team(eng), library.copy(shares = List(annEditsPlan, annEditsReports)),
        "Ann may edit the reports folder, so she unshares it from the engineering team"),
      expect(library, bob, Target.InFolder(reports), Grantee.Team(eng), library,
        "Bob may only view the folder: his request changes nothing"),
      reject(library, bob, Target.Doc(plan), Grantee.Person(ann), library.copy(shares = List(annEditsReports, engViewsReports)),
        "Bob cannot take Ann's share of the plan away"))

  val unshareCode = define { (lib: Term[Library], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    mayEdit(lib, by, what).fold(lib.copy((shares = sharesWithout(lib.shares, what, withWhom))), lib)
  }

  /** Whether `by` may move the document into the folder (or out of every folder): they may edit the document, and the
    * folder exists and they may edit it.
    */
  val mayMove = define { (lib: Term[Library], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    mayEdit(lib, by, Target[Target.Doc](d)) &&
      into.fold(True)(f => lib.folders.exists(folder => folder.id === f) && mayEdit(lib, by, Target[Target.InFolder](f)))
  }
  /** The folders a document moved into a folder is in: that folder and the folders around it; none out of every folder. */
  val foldersAt = define { (lib: Term[Library], into: Term[Option[FolderId]]) =>
    into.fold(List.empty[FolderId])(f => lib.folders.find(folder => folder.id === f).fold(List.empty[FolderId])(folder => folder.folders ++ List(f)))
  }

  val moveContract = Node.contract(move)("MoveContract",
    "Someone who may edit a document moves it into a folder they may edit, or out of every folder: the document is then in that folder and in every folder around it. When anyone else asks, or the folder does not exist, nothing changes.",
    why = "Moving a document changes who may see it, through the folders' shares (Cover), so it needs the right to edit both the document and the folder it goes into.",
    idea = "Who can see and change what"
  )((lib, by, d, into, result) =>
    result === mayMove(lib, by, d, into).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d).fold(doc.copy((folders = foldersAt(lib, into))), doc)))),
      lib))
    .under(accessFollowsShares)
    .examples()(
      expect(library, ann, plan, Some(reports),
        library.copy(documents = List(Document(plan, "Plan", List(reports)), Document(q3Report, "Q3 report", List(reports, q3)))),
        "Ann may edit the plan and the reports folder: the plan moves into it"),
      expect(library, bob, q3Report, None, library, "Bob may only view the Q3 report: it stays where it is"),
      reject(library, ann, plan, Some(FolderId("nowhere")),
        library.copy(documents = List(Document(plan, "Plan", List(FolderId("nowhere"))), Document(q3Report, "Q3 report", List(reports, q3)))),
        "a document never moves into a folder that does not exist"))


  val moveCode = define { (lib: Term[Library], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    val placed = foldersAt(lib, into)
    mayMove(lib, by, d, into).fold(lib.copy((documents = lib.documents.map(doc => (doc.id === d).fold(doc.copy((folders = placed)), doc)))), lib)
  }