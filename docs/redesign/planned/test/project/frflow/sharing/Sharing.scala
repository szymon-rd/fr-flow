package sharing

import frflow.*

// Two of sharing's claims in the owner's forms: `canViewByAccess`, which states its Definition by another applied to
// the same inputs; and `handleAnswers`, about a program, a run whose failing side changes nothing, and the same
// with the failing side written out.

enum Level derives LeanType:
  case View, Edit
final case class Library(viewers: List[BigInt]) derives LeanType
enum Request derives LeanType:
  case Ask(person: BigInt)
  case Grant(person: BigInt)
enum Answer derives LeanType:
  case Access(level: Option[Level])
  case Done
enum Failure derives LeanType:
  case StoreDown

val access = Definition[(Library, BigInt, BigInt, BigInt) => Option[Level]]("a person's access to a document")
val canView = Definition[(Library, BigInt, BigInt, BigInt) => Boolean]("the service's answer: can a person view it")
val handle = Definition[Request => Program[Answer]]("the service handling a request")
val libraryModel = ModelState[Library]("the library the store holds")

val served = define { (lib: Term[Library], r: Term[Request]) =>
  r.on[Request.Ask](_ => lib).on[Request.Grant](p => make[Library](p :: lib.viewers)) }
val answerTo = define { (lib: Term[Library], r: Term[Request]) =>
  r.on[Request.Ask](p => when(lib.viewers.exists(v => v === p))(make[Answer.Access](some[Level](Level.View)))
      .otherwise(make[Answer.Access](none[Level])))
    .on[Request.Grant](_ => Answer.Done) }

val canViewByAccess = Node.claim("A person can view a document exactly when they have some access to it.")(
  forall((lib: Term[Library], t: Term[BigInt], p: Term[BigInt], d: Term[BigInt]) =>
    canView(lib, t, p, d) === (access(lib, t, p, d) =!= none[Level])))

val handleAnswers = Node.claim("A request is answered from the library the store holds, and leaves the " +
    "library it leads to. A request the store fails changes nothing.")(
  forall((r: Term[Request], before: Term[World]) =>
    handle(r).from(before) { (answer, after) =>
      libraryModel.in(after) === served(libraryModel.in(before), r) &&
        answer === answerTo(libraryModel.in(before), r) }.failsChangingNothing[Failure]))

val handleKeepsOnFailure = Node.claim("A request is answered from the library the store holds; a " +
    "failed one leaves the library as it was.")(
  forall((r: Term[Request], before: Term[World]) =>
    handle(r).from(before) { (answer, _) => answer === answerTo(libraryModel.in(before), r) }
      .failing { (_: Term[Failure], after) => libraryModel.in(after) === libraryModel.in(before) }))
