package frflow
package vocabulary

/** A definition of one term: a type (`User := of[UserId]`) or a function of the domain (`authorized := (u, p) => …`). */
final class Subst private[frflow] (val name: String, val target: AnyRef, val isType: Boolean, private[frflow] val typeOf: Option[LeanType[?]],
    val term: Option[Lifted[?]]):
  private lazy val walked = typeOf.map(Types.walk)
  def lean: String = walked.fold(term.fold("")(_.lean))(_.lean)
  def types: List[TypeDecl] = walked.fold(term.fold(Nil)(_.types))(_.types)
  def param: Option[Param[?]] = target match { case p: Param[?] => Some(p); case _ => None }

object Subst:
  def term(p: Param[?], l: Lifted[?]): Subst = Subst(p.name, p, isType = false, None, Some(l))
