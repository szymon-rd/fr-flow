package frflow.cli.say

import frflow.api.node.proving.{CheckState, FindingView, Forbidden, Message, ObligationState, TryView}

/** What Rocq found, in words: a check's state, an obligation's, why a check ended where it did, and what a try
  * showed.
  */
object Findings:
  def check(s: CheckState): String = s match
    case CheckState.Proven     => "proven"
    case CheckState.Open       => "open"
    case CheckState.Failed     => "failed"
    case CheckState.ModelError => "the model does not build"
    case CheckState.Waiting    => "proven, waiting for a part"
    case CheckState.Timeout    => "out of time"
    case CheckState.Unchecked  => "not checked"

  def obligation(s: ObligationState): String = s match
    case ObligationState.Proven      => "proven"
    case ObligationState.Open        => "open"
    case ObligationState.Failed      => "failed"
    case ObligationState.Shown       => "shown"
    case ObligationState.NotShown    => "not shown"
    case ObligationState.Unevaluated => "not evaluated"
    case ObligationState.Unchecked   => "not checked"
    case ObligationState.Timeout     => "out of time"

  /** Its first line, then Rocq's messages (the first line of each, unless `full`). */
  def lines(f: FindingView, full: Boolean): List[String] = f match
    case FindingView.TimedOut          => List("Rocq ran out of time")
    case FindingView.ModelDoesNotBuild(es) => "Rocq does not read the model" :: messages(es, full)
    case FindingView.ProofNotAllowed(what) => "the proof file holds what is not allowed:" ::
        what.map((line, x) => s"  line $line: ${forbidden(x)}")
    case FindingView.LemmasDoNotBuild(es)  =>
      "not proven: it imports the shared lemmas, which are not proven (the error is theirs, not its own proof's)" ::
        messages(es, full)
    case FindingView.NotProven(es)         => "not proven" :: messages(es, full)
    case FindingView.Refuted(tries)        => tries.map(tried)
    case FindingView.DisallowedAxioms(axs) => List(s"its proof rests on axioms not allowed: ${axs.mkString(", ")}")
    case FindingView.StepRefuted(inputs)   =>
      List(s"a step is refuted on: ${inputs.map((n, v) => s"$n = ${Values.value(v)}").mkString(", ")}")

  def messages(es: List[Message], full: Boolean): List[String] = es.map { m =>
    val text = if full then m.text.linesIterator.mkString("\n    ") else m.text.linesIterator.nextOption().getOrElse("")
    s"  ${m.file}:${m.line}: $text"
  }

  /** What Rocq proved of a try: the node says something it should not. */
  def tried(t: TryView): String = t match
    case TryView.Needed(part)              => s"not needed: Rocq proves it without $part"
    case TryView.Vacuous                   => "it holds whatever what it speaks of means: it says nothing"
    case TryView.Restates                  => "it restates its part"
    case TryView.Clash                     => "its parts clash: together they prove anything"
    case TryView.Unsat                     => "it cannot hold"
    case TryView.Idle                      => "doing nothing meets it: say what users can do"
    case TryView.RestatesConjunct(part, i) => s"$part restates conjunct ${i + 1} of it"

  def forbidden(f: Forbidden): String = f match
    case Forbidden.Axiom          => "a statement taken without proof"
    case Forbidden.Admit          => "a proof given up"
    case Forbidden.Import(m)      => s"import $m (not allowed)"
    case Forbidden.LemmaImport(m) => s"import $m in the shared lemmas"
    case Forbidden.Command(w)     => s"the command $w"
