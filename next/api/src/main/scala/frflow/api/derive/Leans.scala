package frflow.api.derive

import frflow.api.node.lean.*
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.TryKind
import frflow.proof.reading.{Diagnostic, NotAllowed}
import frflow.proof.verdict.{CheckStatus, Finding, ObligationStatus, Result}

/** What Lean found, as the front ends see it: each of `proof.verdict`'s values as its view, case for case. */
private[api] object Leans:
  val Unchecked: CheckState = CheckState.Unchecked

  def state(s: CheckStatus): CheckState = s match
    case CheckStatus.Proven     => CheckState.Proven
    case CheckStatus.Open       => CheckState.Open
    case CheckStatus.Failed     => CheckState.Failed
    case CheckStatus.ModelError => CheckState.ModelError
    case CheckStatus.Waiting    => CheckState.Waiting
    case CheckStatus.Timeout    => CheckState.Timeout
    case CheckStatus.Unchecked  => CheckState.Unchecked

  def state(s: ObligationStatus): ObligationState = s match
    case ObligationStatus.Proven      => ObligationState.Proven
    case ObligationStatus.Open        => ObligationState.Open
    case ObligationStatus.Failed      => ObligationState.Failed
    case ObligationStatus.Shown       => ObligationState.Shown
    case ObligationStatus.NotShown    => ObligationState.NotShown
    case ObligationStatus.Unevaluated => ObligationState.Unevaluated
    case ObligationStatus.Unchecked   => ObligationState.Unchecked
    case ObligationStatus.Timeout     => ObligationState.Timeout

  def of(r: Result): ObligationView =
    ObligationView(LowerObligation.name(r.name).text, state(r.status), r.messages.map(message))

  def message(d: Diagnostic): Message = Message(d.file, d.line, d.error, d.message)

  def finding(f: Finding): FindingView = f match
    case Finding.LeanTimedOut           => FindingView.LeanTimedOut
    case Finding.ModelDoesNotBuild(es)  => FindingView.ModelDoesNotBuild(es.map(message))
    case Finding.ProofNotAllowed(what)  => FindingView.ProofNotAllowed(what.map((l, n) => l -> forbidden(n)))
    case Finding.LemmasDoNotBuild(es)   => FindingView.LemmasDoNotBuild(es.map(message))
    case Finding.NotProven(es)          => FindingView.NotProven(es.map(message))
    case Finding.Refuted(tries)         => FindingView.Refuted(tries.map(tried))
    case Finding.DisallowedAxioms(axs)  => FindingView.DisallowedAxioms(axs)
    case Finding.StepRefuted(inputs)    => FindingView.StepRefuted(inputs)

  def tried(k: TryKind): TryView = k match
    case TryKind.Needed(p)              => TryView.Needed(p)
    case TryKind.Vacuous                => TryView.Vacuous
    case TryKind.Restates               => TryView.Restates
    case TryKind.Clash                  => TryView.Clash
    case TryKind.Unsat                  => TryView.Unsat
    case TryKind.Idle                   => TryView.Idle
    case TryKind.RestatesConjunct(p, i) => TryView.RestatesConjunct(p, i)

  def forbidden(n: NotAllowed): Forbidden = n match
    case NotAllowed.Axiom          => Forbidden.Axiom
    case NotAllowed.Admit          => Forbidden.Admit
    case NotAllowed.Unsafe         => Forbidden.Unsafe
    case NotAllowed.Opaque         => Forbidden.Opaque
    case NotAllowed.ImplementedBy  => Forbidden.ImplementedBy
    case NotAllowed.Extern         => Forbidden.Extern
    case NotAllowed.NativeDecide   => Forbidden.NativeDecide
    case NotAllowed.Attribute      => Forbidden.Attribute
    case NotAllowed.SetOption(o)   => Forbidden.SetOption(o)
    case NotAllowed.Metaprogram(c) => Forbidden.Metaprogram(c)
    case NotAllowed.Import(m)      => Forbidden.Import(m)
    case NotAllowed.LemmaImport(m) => Forbidden.LemmaImport(m)
    case NotAllowed.Command(w)     => Forbidden.Command(w)
