package sharing.domain

import frflow.*

/** A person who uses the library, named by their account. */
final case class PersonId(name: String)
object PersonId extends Data[PersonId]

/** A team, named by its handle. */
final case class TeamId(name: String)
object TeamId extends Data[TeamId]

/** A team and the people in it. Teams contain people only: a team is never a member of another team. */
final case class Team(id: TeamId, members: List[PersonId])
object Team extends Data[Team]
