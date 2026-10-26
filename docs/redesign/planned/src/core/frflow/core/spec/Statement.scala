package frflow.core.spec

import cats.data.NonEmptyList
import frflow.core.example.{CallExample, Given, RunExample}
import frflow.core.expr.{Expr, Lambda}
import frflow.core.name.{ModelName, NodeId, RelPath, SymbolName}

/** What a node says, one case per kind, each with only its own data. */
enum Statement:
  case Claim(formula: Written[Expr], expects: List[Expectation])
  case Invariant(rule: Written[Lambda], scope: List[NodeId])
  case Contract(op: SymbolName, promise: Promise[CallExample], reliance: Reliance)
  case FlowContract(op: SymbolName, promise: Promise[RunExample], failure: Option[FailureClause], reliance: Reliance)
  case Fact(formula: Written[Expr])
  case AssumedCall(op: SymbolName, promise: Promise[CallExample])
  case Model(model: ModelName)
  case Definition(fixes: NonEmptyList[Fixing])
  case Design(governs: NonEmptyList[RelPath])

  def kind: NodeKind = this match
    case Claim(_, _)                        => NodeKind.Claim
    case Invariant(_, _)                    => NodeKind.Invariant
    case Contract(_, _, _) | FlowContract(_, _, _, _) => NodeKind.Contract
    case Fact(_) | AssumedCall(_, _) | Model(_) => NodeKind.Assumption
    case Definition(_)                      => NodeKind.Definition
    case Design(_)                          => NodeKind.Design

  def operation: Option[SymbolName] = this match
    case Contract(op, _, _)        => Some(op)
    case FlowContract(op, _, _, _) => Some(op)
    case AssumedCall(op, _)        => Some(op)
    case _                         => None

  /** The expressions it says things with, in order. */
  def exprs: List[Expr] = this match
    case Claim(f, es)                => f.value :: es.map(_.consequence.value)
    case Invariant(r, _)             => List(r.value.body)
    case Contract(_, p, _)           => p.exprs
    case FlowContract(_, p, fail, _) => p.exprs ++ fail.toList.flatMap(_.exprs)
    case Fact(f)                     => List(f.value)
    case AssumedCall(_, p)           => p.exprs
    case Definition(fs)              => fs.toList.flatMap(_.exprs)
    case Model(_) | Design(_)        => Nil

  /** What its examples give values to. */
  def givens: List[Given] = this match
    case Contract(_, p, _)        => p.examples.flatMap(_.givens)
    case FlowContract(_, p, _, _) => p.examples.flatMap(_.givens)
    case AssumedCall(_, p)        => p.examples.flatMap(_.givens)
    case _                        => Nil

  /** Lean states it: a model is decided, a definition and a design state nothing. */
  def stated: Boolean = this match
    case Model(_) | Definition(_) | Design(_) => false
    case _                                    => true
