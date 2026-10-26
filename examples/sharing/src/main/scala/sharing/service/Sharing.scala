package sharing.service

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.inForce

/** The sharing rules: what a person can do with a document, and how sharing and moving change the library. Each
  * method is a function of the library and of the moment it is asked at (`now`); the effects (keeping the library,
  * reading the clock, answering requests) live in `sharing.http`.
  */
trait Sharing:
  /** A person's access to a document now: edit, view, or none. */
  def access(library: Library, now: BigInt, person: PersonId, doc: DocumentId): Option[Level]
  def canView(library: Library, now: BigInt, person: PersonId, doc: DocumentId): Boolean
  def canEdit(library: Library, now: BigInt, person: PersonId, doc: DocumentId): Boolean
  /** The library after `by` shares: `share` says what, with whom, at which level and until when. */
  def share(library: Library, now: BigInt, by: PersonId, share: Share): Library
  /** The library after `by` unshares `what` from `withWhom`. */
  def unshare(library: Library, now: BigInt, by: PersonId, what: Target, withWhom: Grantee): Library
  /** The library after `by` moves `doc` into a folder, or out of every folder (`None`). */
  def move(library: Library, now: BigInt, by: PersonId, doc: DocumentId, into: Option[FolderId]): Library

/** Sharing's operations: for each method, its contract and its code. */
object Sharing:
  import Demo.*

  val access = Param[(Library, BigInt, PersonId, DocumentId) => Option[Level]]("access", "a person's access to a document at a moment, as the service works it out")
  val canView = Param[(Library, BigInt, PersonId, DocumentId) => Boolean]("canView", "the service's answer to whether a person can view a document")
  val canEdit = Param[(Library, BigInt, PersonId, DocumentId) => Boolean]("canEdit", "the service's answer to whether a person can edit a document")
  val share = Param[(Library, BigInt, PersonId, Share) => Library]("share", "the library after someone asks to share a document or folder")
  val unshare = Param[(Library, BigInt, PersonId, Target, Grantee) => Library]("unshare", "the library after someone asks to unshare a document or folder")
  val move = Param[(Library, BigInt, PersonId, DocumentId, Option[FolderId]) => Library]("move", "the library after someone asks to move a document")

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

  /** The shares, less any of `what` with `withWhom`. Declared before AccessContract, a part of Invitations' branch:
    * Invitations, set up from there, uses it. */
  val sharesWithout = define { (ss: Term[List[Share]], what: Term[Target], withWhom: Term[Grantee]) =>
    ss.filterNot(s => s.what === what && s.withWhom === withWhom)
  }

  val accessContract = Node.contract(access)("AccessContract",
    "A person's access to a document not in the trash is worked out from their teams and the document's folders: among the shares in force with them or one of their teams, of the document or one of the folders around it, it is edit if one is an edit share, view if there is any, and none otherwise. A document in the trash gives no access.",
    why = "This is how the service finds the shares that matter without asking every share whether it reaches the person and covers the document: it lists who a share must be with and what it must be of, once each. That this finds exactly the shares the meaning names (Reach, Cover) is what the purpose's proof shows.",
    idea = "Who can see and change what"
  )((lib, t, p, d, result) => result === inTrash(lib, d).fold(none[Level],
      strongest(lib.shares.filter(s => inForce(s, t) && granteesOf(lib, p).contains(s.withWhom) && placesOf(lib, d).contains(s.what)))))
    .under(accessFollowsShares, sharing.invitations.Invitations.invitationsAreOffers)
    .examples()(
      expect(library, now, bob, q3Report, Some(Level.View), "Bob's team may view the reports folder, which the Q3 report is in"),
      expect(library, now, ann, q3Report, Some(Level.Edit), "Ann may edit the reports folder"),
      expect(library, now, cat, plan, None, "nothing is shared with Cat"),
      expect(library.copy(shares = bobViewsPlanForAnHour :: library.shares), now, bob, plan, Some(Level.View), "Bob's share of the plan is in force"),
      expect(library.copy(shares = bobViewsPlanForAnHour :: library.shares), now + 3600, bob, plan, None, "Bob's share of the plan has ended"),
      expect(library.copy(documents = List(planTrashed, q3ReportDoc)), now, ann, plan, None, "the plan is in the trash"),
      never(library, now, bob, plan, Some(Level.View), "nothing shares the plan with Bob or his team"),
      never(library, now, ann, plan, Some(Level.View), "Ann's share of the plan is an edit share: her access is edit"))

  /** Access, worked out: none in the trash; else the shares in force with the person or one of their teams, of the
    * document or a folder around it; the strongest of them.
    */
  val accessCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    val (grantees, places) = (granteesOf(lib, p), placesOf(lib, d))
    inTrash(lib, d).fold(none[Level], strongest(lib.shares.filter(s => inForce(s, t) && grantees.contains(s.withWhom) && places.contains(s.what))))
  }

  // ---------------------------------------------------------------------------
  // canView, canEdit: what the access allows
  // ---------------------------------------------------------------------------

  val canViewContract = Node.contract(canView)("CanViewContract",
    "A person can view a document exactly when they have some access to it.",
    why = "Viewing needs a share of any level, and editing includes viewing (Q1).",
    idea = "Who can see and change what"
  )((lib, t, p, d, result) => result === access(lib, t, p, d).isDefined)
    .under(accessFollowsShares)
    .examples()(
      expect(library, now, bob, q3Report, true, "Bob's team may view the reports folder"),
      expect(library, now, cat, q3Report, false, "nothing is shared with Cat"),
      never(library, now, cat, plan, true, "Cat has no access to the plan"))

  val canViewCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) => access(lib, t, p, d).isDefined }

  val canEditContract = Node.contract(canEdit)("CanEditContract",
    "A person can edit a document exactly when their access to it is edit.",
    why = "Only an edit share lets someone change a document (Q1).",
    idea = "Who can see and change what"
  )((lib, t, p, d, result) => result === (access(lib, t, p, d) === some(Level.Edit: Term[Level])))
    .under(accessFollowsShares)
    .examples()(
      expect(library, now, ann, q3Report, true, "Ann may edit the reports folder, around the Q3 report"),
      expect(library, now, bob, q3Report, false, "Bob's team may only view it"),
      never(library, now, bob, q3Report, true, "a view share never lets anyone edit"))

  val canEditCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId]) =>
    access(lib, t, p, d) === some(Level.Edit: Term[Level])
  }

  // ---------------------------------------------------------------------------
  // share, unshare, move: changes, made only by someone who may edit what they change
  // ---------------------------------------------------------------------------

  private val bobViewsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val catViewsReports = Share(Target.InFolder(reports), Grantee.Person(cat), Level.View, None)
  private val bobEditsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None)

  val shareContract = Node.contract(share)("ShareContract",
    "Someone who may edit a document or folder shares it with a person or a team at a level, for good or until a time: the new share takes the place of any earlier share of it with them, unless it is the owner's share of their own document, which stays. When anyone else asks, nothing changes.",
    why = "Anyone who can edit a document can share it (Q2), and a person or team has one share of a thing at a time, so sharing again changes the level and the end rather than adding a second share (Q6); the owner's own share is not replaced, so it never becomes a view share or one that ends (Q14).",
    idea = "Who can see and change what"
  )((lib, t, by, s, result) =>
    result === (mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom)).fold(lib.copy((shares = s :: sharesWithout(lib.shares, s.what, s.withWhom))), lib))
    .under(accessFollowsShares, sharing.ownership.Ownership.ownersKeepTheirDocuments)
    .examples()(
      expect(library, now, ann, bobViewsPlan, library.copy(shares = bobViewsPlan :: library.shares),
        "Ann may edit the plan, so she shares it with Bob"),
      expect(library, now, ann, bobViewsPlanForAnHour, library.copy(shares = bobViewsPlanForAnHour :: library.shares),
        "Ann shares the plan with Bob for an hour"),
      expect(library, now, bob, Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None), library,
        "Bob may not edit the plan: his request changes nothing"),
      never(library, now, bob, catViewsReports, library.copy(shares = catViewsReports :: library.shares),
        "Bob may only view the reports folder, so he cannot share it"),
      expect(library.copy(shares = bobEditsPlan :: library.shares), now, bob, Share(Target.Doc(plan), Grantee.Person(ann), Level.View, Some(now + 3600)),
        library.copy(shares = bobEditsPlan :: library.shares), "Bob may edit the plan, but Ann owns it: her edit share stays as it is"))

  val shareCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
    (mayEdit(lib, t, by, s.what) && !ownedBy(lib, s.what, s.withWhom)).fold(lib.copy((shares = s :: sharesWithout(lib.shares, s.what, s.withWhom))), lib)
  }

  val unshareContract = Node.contract(unshare)("UnshareContract",
    "Someone who may edit a document or folder unshares it from a person or a team: their share of it goes, unless it is the owner's share of their own document. When anyone else asks, nothing changes.",
    why = "Unsharing is changing who a document is shared with, which only someone who may edit it does (Q2); the owner's own share stays, so the owner always may edit (Q14).",
    idea = "Who can see and change what"
  )((lib, t, by, what, withWhom, result) =>
    result === (mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom)).fold(lib.copy((shares = sharesWithout(lib.shares, what, withWhom))), lib))
    .under(accessFollowsShares, sharing.ownership.Ownership.ownersKeepTheirDocuments)
    .examples()(
      expect(library, now, ann, Target.InFolder(reports), Grantee.Team(eng), library.copy(shares = List(annEditsPlan, annEditsReports)),
        "Ann may edit the reports folder, so she unshares it from the engineering team"),
      expect(library, now, bob, Target.InFolder(reports), Grantee.Team(eng), library,
        "Bob may only view the folder: his request changes nothing"),
      expect(library.copy(shares = bobEditsPlan :: library.shares), now, bob, Target.Doc(plan), Grantee.Person(ann),
        library.copy(shares = bobEditsPlan :: library.shares), "Bob may edit the plan, but Ann owns it: her share stays"),
      never(library, now, bob, Target.Doc(plan), Grantee.Person(ann), library.copy(shares = List(annEditsReports, engViewsReports)),
        "Bob cannot take Ann's share of the plan away"))

  val unshareCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
    (mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom)).fold(lib.copy((shares = sharesWithout(lib.shares, what, withWhom))), lib)
  }

  /** Whether `by` may move the document into the folder (or out of every folder): they may edit the document, and the
    * folder exists and they may edit it.
    */
  val mayMove = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    mayEdit(lib, t, by, Target[Target.Doc](d)) &&
      into.fold(True)(f => lib.folders.exists(folder => folder.id === f) && mayEdit(lib, t, by, Target[Target.InFolder](f)))
  }
  /** The folders a document moved into a folder is in: that folder and the folders around it; none out of every folder. */
  val foldersAt = define { (lib: Term[Library], into: Term[Option[FolderId]]) =>
    into.fold(List.empty[FolderId])(f => lib.folders.find(folder => folder.id === f).fold(List.empty[FolderId])(folder => folder.folders ++ List(f)))
  }

  val moveContract = Node.contract(move)("MoveContract",
    "Someone who may edit a document moves it into a folder they may edit, or out of every folder: the document is then in that folder and in every folder around it. When anyone else asks, or the folder does not exist, nothing changes.",
    why = "Moving a document changes who may see it, through the folders' shares (Cover), so it needs the right to edit both the document and the folder it goes into.",
    idea = "Who can see and change what"
  )((lib, t, by, d, into, result) =>
    result === mayMove(lib, t, by, d, into).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d).fold(doc.copy((folders = foldersAt(lib, into))), doc)))),
      lib))
    .under(accessFollowsShares)
    .examples()(
      expect(library, now, ann, plan, Some(reports),
        library.copy(documents = List(planDoc.copy(folders = List(reports)), q3ReportDoc)),
        "Ann may edit the plan and the reports folder: the plan moves into it"),
      expect(library, now, bob, q3Report, None, library, "Bob may only view the Q3 report: it stays where it is"),
      never(library, now, ann, plan, Some(FolderId("nowhere")),
        library.copy(documents = List(planDoc.copy(folders = List(FolderId("nowhere"))), q3ReportDoc)),
        "a document never moves into a folder that does not exist"))

  val moveCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], into: Term[Option[FolderId]]) =>
    val placed = foldersAt(lib, into)
    mayMove(lib, t, by, d, into).fold(lib.copy((documents = lib.documents.map(doc => (doc.id === d).fold(doc.copy((folders = placed)), doc)))), lib)
  }
