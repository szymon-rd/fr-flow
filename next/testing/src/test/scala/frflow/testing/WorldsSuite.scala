package frflow.testing

import frflow.*
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.eval.{Races, Semantics}
import frflow.eval.flow.{Shelf, Trouble}
import frflow.testing.derive.Derive
import frflow.testing.report.Failure

/** Drawn worlds carry the faults a failing boundary's calls take and the races' winners, so a generated test of a
  * claim about a run takes a failing call's error path, and lets a race's right side win.
  */
class WorldsSuite extends munit.FunSuite:
  /** Puts a number on the shelf, saying it did, or that it could not when the shelf is down. */
  private final class Puts[F[_]](s: Shelf[F, Term])(using f: Flow[F]):
    def run(n: Term[BigInt]): F[Term[Boolean]] =
      f.handle[Trouble, Term[Boolean]](f.as(s.put(n), True))(_ => f.pure(False))

  /** Reads the shelf after putting a number, raced against reading it. */
  private final class Races_[F[_]](s: Shelf[F, Term])(using f: Flow[F]):
    def run(n: Term[BigInt]): F[Term[Either[List[BigInt], List[BigInt]]]] =
      f.race(f.flatMap(s.put(n))(_ => s.items), s.items)

  private val putting = Definition[BigInt => Program[Boolean]]("putting a number on the shelf")
  private val racing = Definition[BigInt => Program[Either[List[BigInt], List[BigInt]]]]("reading, raced")
  private val puts = program { (n: Term[BigInt]) => Puts(Shelf.shelf.recording).run(n) }
  private val races = program { (n: Term[BigInt]) => Races_(Shelf.shelf.recording).run(n) }

  private val putIsKept = Node.claim("A number put is on the shelf after.")(
    forall((n: Term[BigInt], before: Term[World]) =>
      putting(n).from(before) { (_, after) => Shelf.kept.in(after).contains(n) }))
  private val readSeesPut = Node.claim("What is read holds the number put.")(
    forall((n: Term[BigInt], before: Term[World]) =>
      racing(n).from(before) { (read, _) => read.fold(xs => xs.contains(n), ys => ys.contains(n)) }))

  private val kb = KnowledgeBase("Shelves")((Shelf.knowledge.nodes ++ List(putIsKept, readSeesPut))*)
    .implementProven(putting)(puts).implementProven(racing)(races)
  private val e = kb.elaborated.fold(es => fail(es.toString), identity)

  private def failingWorld(claim: String): List[(Value, Option[Value])] =
    PropertyTests(Semantics(e), e.theory).of(NodeId(claim), Plan(Settings(300, Seed(1)), Nil), Derive.of(e, Nil))
      .flatMap(_.failure).toList.collect { case Failure.Call(List(_, w @ Value.World(states, _)), _, _, _) =>
        w -> states.find(_._1 == Races.model).map(_._2) }

  test("a claim broken only when a call fails is found on a world whose first fault fails it") {
    failingWorld("putIsKept") match
      case List((Value.World(_, faults), _)) => assertEquals(faults.headOption, Some(true))
      case other                             => fail(s"not found: $other")
  }

  test("a claim broken only when the right side of a race wins is found on a world whose race it wins") {
    failingWorld("readSeesPut") match
      case List((_, Some(Value.Many(races)))) => assertEquals(races.headOption, Some(Value.Bool(false)))
      case other                                              => fail(s"not found: $other")
  }
