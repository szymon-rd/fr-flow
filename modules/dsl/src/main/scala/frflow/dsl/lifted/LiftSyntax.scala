package frflow.dsl.lifted

import frflow.core.name.DefName
import frflow.core.ty.Ty
import frflow.dsl.build.{Fault, Source, WrittenAt}
import frflow.dsl.node.AlwaysSyntax
import frflow.dsl.term.{Notes, Term, Terms, TermSyntax}

/** `contractOf[T]`: a type's contract as a node's formula. */
object LiftSyntax:
  /** `always` of a type's contract, a node's whole formula (`Node.assumption("…")(contractOf[Booking])`: an
    * assumption of a type from outside, a claim of one the code makes): the rule a define named as the node's val,
    * as `always[T](x => …)` makes one. Of a type whose spec states no contract, a fault on the node.
    */
  inline def contractOf[A](using s: FrSpec[A]): Term[Boolean] =
    stating(s, DefName(Source.valName), WrittenAt.in(Source.here))

  def stating[A](s: FrSpec[A], name: DefName, at: WrittenAt): Term[Boolean] = s.contract.fold(
    Term.noted(Notes.fault(Fault.NoContract(Ty.names(s.ty).headOption.fold(s.ty.toString)(_.value))))(
      TermSyntax.True.run))(c => Terms.always[A](c.written.params.headOption.getOrElse("x"),
        AlwaysSyntax.applied(Lifting.stated[A](name, at, c.written)(c.rule)(using s)))(using s))
