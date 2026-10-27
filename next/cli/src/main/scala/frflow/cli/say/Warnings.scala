package frflow.cli.say

import frflow.api.view.Warning
import frflow.decision.ledger.{Action, Decision, Uncounted}

/** What `status` warns of, in words (docs/USAGE.md, Warnings), and why a decision does not count. */
object Warnings:
  def text(w: Warning): String = (deciding orElse code orElse proofs)(w)

  private val deciding: PartialFunction[Warning, String] =
    case Warning.NoKey                    =>
      "no signing key (FRFLOW_KEY, or ~/.config/frflow/signing.key): nothing can be decided here"
    case Warning.DecidersUncommitted      =>
      ".frflow/deciders differs from the committed list, which is the one that counts: commit it, or restore it"
    case Warning.NotCounted(id, d, why)   => s"${verb(d.action)} of $id by ${d.author.by} does not count: " +
        uncounted(why, d)

  private val code: PartialFunction[Warning, String] =
    case Warning.GovernedTwice(f, by) => s"$f is governed by ${by.mkString(" and ")}: each would review it as its own"
    case Warning.Ungoverned(f)            => s"no node governs $f: code there changes unnoticed " +
        "(give it a home: the claim whose code it is, or a design node)"
    case Warning.GovernedMissing(f, by)   => s"$by governs $f, which names no file of the project"

  private val proofs: PartialFunction[Warning, String] =
    case Warning.ProofFileOfNoNode(f)     => s"$f is no node's proof file (renamed or removed?): it proves nothing"
    case Warning.ConsistencyNotProven(ns) => s"consistency not proven: ${ns.mkString(", ")} " +
        "(no witness Lean checked for what they leave open)"
    case Warning.StartNotProven(id)       =>
      s"$id: the states its store starts in are not proven to meet it (start_$id; say what it starts with)"
    case Warning.NotChecked(id)           => s"$id is not checked: no parts prove it, no proven code is checked " +
        "against it, and the plain Scala it is about has no Scala value to test against"
    case Warning.Restates(id, part)       => s"$id restates $part: Lean proves them equivalent, so it says nothing " +
        "of its own"

  def uncounted(u: Uncounted, d: Decision): String = u match
    case Uncounted.NoDeciders  => "no deciders' list is committed (init --as NAME writes one; commit it)"
    case Uncounted.NotListed   => s"its key is not listed under ${d.author.by} in the committed deciders' list"
    case Uncounted.NotVerified => "its signature does not verify"
    case Uncounted.Rewritten   => "what was committed of this node's decisions was taken out or changed " +
        "(restore .frflow/ledger.json from the last commit, or a listed decider runs rebase)"
    case Uncounted.Unreadable  =>
      "a committed version of the ledger does not read, so nothing counts (a listed decider runs rebase)"

  def verb(a: Action): String = a match
    case Action.Accept  => "acceptance"
    case Action.Confirm => "confirmation"
    case Action.Reject  => "rejection"
    case Action.Revisit => "revisit"
    case Action.Remove  => "agreement it is gone"
