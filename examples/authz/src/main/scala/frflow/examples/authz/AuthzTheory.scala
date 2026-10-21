package frflow.examples.authz

import frflow.dsl.*
import frflow.model.NodeSpec

/** Theory of an authorization platform.
  *
  * T0  NoUnauthorizedAccess   what must hold, independent of mechanism
  * └── T1  AuthnThenAuthz     access is mediated by sessions and the current policy
  */
object AuthzTheory extends TheoryDef("Authz"):

  vocabulary(
    opaqueType("User", "A principal: a person or a service that can act on the system."),
    opaqueType("Resource", "Anything access to which is controlled."),
    opaqueType("Action", "An operation a principal can perform on a resource."),
    typeAlias("Token", "Nat", "Identifier of a bearer credential issued at login.")
  )

  val A1 = assumption(
    id = "A1",
    name = "PresenterIsSessionPrincipal",
    statement = "A request presenting a token bound to principal u is issued by u.",
    justification =
      "Tokens are issued only to authenticated principals and are unforgeable and not shared. " +
        "To be discharged by the authentication refinement (T2a) under the unforgeability of signatures."
  )

  // ---------------------------------------------------------------------------
  // T0: the security goal
  // ---------------------------------------------------------------------------

  val T0 = root(
    id = "T0",
    name = "NoUnauthorizedAccess",
    statement = "Every recorded access was permitted by the policy in force when it was decided.",
    rationale =
      "States the security goal independently of any mechanism. Policies change over time, " +
        "so the goal is relative to the policy version in force at decision time; past versions are immutable."
  )(
    NodeSpec(
      defs = Seq(
        lean("""
          |/-- One access performed by `user`, decided under policy version `ver`. -/
          |structure Entry where
          |  user : User
          |  res  : Resource
          |  act  : Action
          |  ver  : Nat
          |""")
      ),
      state = Seq(
        field("version", "Nat", "Current policy version."),
        field("policy", "Nat → User → Resource → Action → Prop", "Policy history, indexed by version."),
        field("log", "List Entry", "Accesses that occurred, most recent first.")
      ),
      init = lean("s.version = 0 ∧ s.log = []"),
      events = Seq(
        event("access")
          .doc("A user performs an action on a resource.")
          .params("u" -> "User", "r" -> "Resource", "a" -> "Action")
          .check("s.policy s.version p.u p.r p.a")
          .act("{ s with log := ⟨p.u, p.r, p.a, s.version⟩ :: s.log }"),
        event("setPolicy")
          .doc("An administrator publishes a new policy version.")
          .params("pol" -> "User → Resource → Action → Prop")
          .act(
            "{ s with version := s.version + 1, " +
              "policy := fun v => if v = s.version + 1 then p.pol else s.policy v }"
          )
      ),
      invariants = Seq(
        invariant(
          "Safe",
          "∀ e ∈ s.log, e.ver ≤ s.version ∧ s.policy e.ver e.user e.res e.act",
          "Every logged access is permitted by the (immutable) policy version it was decided under."
        )
      )
    )
  )

  // ---------------------------------------------------------------------------
  // T1: authentication establishes a session principal, authorization decides
  // ---------------------------------------------------------------------------

  val T1 = T0.refine(
    id = "T1",
    name = "AuthnThenAuthz",
    statement = "Access is granted only to the principal bound to the presented token, under the current policy.",
    rationale =
      "Separates identity (sessions created at login) from permission (policy decision). " +
        "The system cannot observe who sends a request, only which token is presented, so the link " +
        "between the token and the real requester is an explicit environment assumption (A1)."
  )(
    link = link(abs = "{ version := s.version, policy := s.policy, log := s.log }"),
    spec = NodeSpec(
      state = Seq(
        field("version", "Nat"),
        field("policy", "Nat → User → Resource → Action → Prop"),
        field("log", "List T0.Entry"),
        field("sessions", "Token → Option User", "Principal bound to each issued token.")
      ),
      init = lean("s.version = 0 ∧ s.log = [] ∧ ∀ t, s.sessions t = none"),
      events = Seq(
        event("access")
          .doc("A request presenting token `t` asks to perform `a` on `r`. `actor` is the real requester (ghost).")
          .params("actor" -> "User", "t" -> "Token", "u" -> "User", "r" -> "Resource", "a" -> "Action")
          .assume(A1, "∀ v, s.sessions p.t = some v → v = p.actor")
          .check("s.sessions p.t = some p.u")
          .check("s.policy s.version p.u p.r p.a")
          .act("{ s with log := ⟨p.u, p.r, p.a, s.version⟩ :: s.log }")
          .refines("access", witness = "{ u := p.actor, r := p.r, a := p.a }"),
        event("login")
          .doc("An authenticated principal receives a fresh token.")
          .params("u" -> "User", "t" -> "Token")
          .check("s.sessions p.t = none")
          .act("{ s with sessions := fun t' => if t' = p.t then some p.u else s.sessions t' }")
          .refinesSkip,
        event("logout")
          .doc("A token is revoked.")
          .params("t" -> "Token")
          .act("{ s with sessions := fun t' => if t' = p.t then none else s.sessions t' }")
          .refinesSkip,
        event("setPolicy")
          .params("pol" -> "User → Resource → Action → Prop")
          .act(
            "{ s with version := s.version + 1, " +
              "policy := fun v => if v = s.version + 1 then p.pol else s.policy v }"
          )
          .refines("setPolicy", witness = "{ pol := p.pol }")
      )
    )
  )
