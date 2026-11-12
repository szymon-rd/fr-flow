package frflow.core.spec

import cats.data.NonEmptyList
import frflow.core.expr.Expr
import frflow.core.name.{RelPath, SymbolName}

/** What a node says: one case per kind of node, and no other (owner §15). A claim is proven (or tested, where a
  * Definition it mentions is plain Scala), an assumption trusted, a design a decision about code no proof covers.
  * How each is checked is derived from its formula and from what defines each Definition it mentions
  * (`analysis.Checking`), never written beside it.
  */
enum Statement:
  case Claim(formula: Written[Expr], reliance: Reliance)
  case Assumption(formula: Written[Expr])
  case Design(governs: NonEmptyList[RelPath])

  def kind: NodeKind = this match
    case Claim(_, _)   => NodeKind.Claim
    case Assumption(_) => NodeKind.Assumption
    case Design(_)     => NodeKind.Design

  def said: Option[Written[Expr]] = this match
    case Claim(f, _)   => Some(f)
    case Assumption(f) => Some(f)
    case Design(_)     => None

  /** What its leading quantifier ranges over; a design ranges over nothing. */
  def range: Option[Range] = said.map(f => Range.of(f.value))

  /** A rule: a statement of `always`, claimed or assumed. Placed below a statement it serves, it is no part of that
    * statement's step: Lean already has it of every value (2.4).
    */
  def rule: Boolean = range.exists(_ != Range.Possible)

  /** The call of one Definition it reads as: what a test of that Definition's code checks a call against. */
  def call: Option[CallForm] = said.flatMap(CallForms.of)

  def definition: Option[SymbolName] = call.map(_.definition)

  def relied: Reliance = this match
    case Claim(_, r) => r
    case _           => Reliance.Relied

  /** The expressions it says things with, in order. */
  def exprs: List[Expr] = said.toList.map(_.value)

  /** The prover states it: a claim or an assumption. */
  def stated: Boolean = said.isDefined
