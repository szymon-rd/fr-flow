package sharing.domain

import frflow.*

/** A person who uses the library, named by their account. */
final case class PersonId(name: String) derives LeanType

/** A team, named by its handle. */
final case class TeamId(name: String) derives LeanType

/** A team and the people in it. Teams contain people only: a team is never a member of another team. */
final case class Team(id: TeamId, members: List[PersonId]) derives LeanType
