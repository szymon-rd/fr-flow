package frflow.cli.say

import frflow.core.analysis.Problem
import frflow.core.analysis.outside.Premise

/** What keeps a FrModel from being checked, in words: each problem names what is wrong, where, and what to do. */
object Problems:
  def text(p: Problem): String = (graph orElse outside orElse vocabulary orElse programs)(p)

  private val graph: PartialFunction[Problem, String] =
    case Problem.DuplicateId(id)            => s"two nodes are named $id"
    case Problem.NoRoot                     => "no root statement: every node refines another (state the purpose)"
    case Problem.AboveItself(id)            => s"$id is above itself: its parents lead back to it"
    case Problem.ParentOutside(id, parent)  => s"$id refines $parent, which is not in the FrModel"
    case Problem.DesignWithoutParent(id)    => s"the design $id refines nothing: a design is under the claim it serves"
    case Problem.UnderDesign(id, design)    => s"$id refines the design $design: nothing refines a design"
    case Problem.PremiseNotAssumed(id, p)   => s"$id assumes $p, which is no assumption: place a claim of always " +
        s"below the statement it serves ($p.refines($id))"
    case Problem.PremiseBelow(id, p)        =>
      s"$id assumes $p, which rests on $id: the two could never be decided in order"

  private val outside: PartialFunction[Problem, String] =
    case Problem.OutsideAsPart(fact, whole) => s"$fact, an assumption about the outside, refines $whole: assume it " +
        s"instead ($whole.assuming($fact))"
    case Problem.PremiseMissing(id, n, by)  => s"$id rests on ${premise(n)}, which its .assuming does not list" +
        by.fold(" (no assumption says it yet)")(b => s" (add .assuming($b))")
    case Problem.PremiseNotNeeded(id, p)    => s"$id assumes $p, which its check does not rest on"
    case Problem.AlwaysNotReached(a, t, at) => s"the always $a is about ${Values.ty(t)} inside ${at.says}, where no " +
        "check reaches it yet"

  private val vocabulary: PartialFunction[Problem, String] =
    case Problem.ReservedName(name)         => s"$name is a reserved name: name it otherwise"
    case Problem.DeclaredTwice(name)        => s"$name is declared twice"
    case Problem.CodeOnlyInStatement(id, s, t) => s"$id speaks of ${s.value}: ${Faults.codeOnly(t)}"
    case Problem.SaidToExist(t, at)         => s"${at.says} is said to exist of ${Values.ty(t)}, which holds a " +
        "Scala Int or Long (by the statement, a rule of always, or the theory's consistency): Rocq's integers are " +
        "unbounded, so it could find one Scala cannot hold; use BigInt"
    case Problem.Undefined(d)               => s"code calls ${d.value}, and nothing gives it a meaning: list a " +
        s"Definition of it in the model (${d.value}.define(…), .defineTested(…), .defineValue(…), .provided)"
    case Problem.DeclarationInCode(c, d)    => s"${c.value} is code and reaches ${d.value}, a word only statements " +
        "read: give it a Definition, or keep it out of code"
    case Problem.CodeWithoutClaim(d) => s"${d.value} has code, but no statement mentions it: there is nothing to " +
        "check it against"

  private val programs: PartialFunction[Problem, String] =
    case Problem.RestsOnItself(ids)         => s"${ids.mkString(", ")} are each proven, through the others, from itself"

  private def premise(p: Premise): String = p match
    case Premise.FromOutside(t)   => s"what the values of ${Values.ty(t)} from outside meet (an assumption of " +
        s"always[${Values.ty(t)}])"
