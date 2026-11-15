package frflow.dsl.compiled.source

import scala.quoted.Quotes

/** How the tree read names what a class or a package declares (`SourceSyms.member`), for what names it elsewhere
  * by the same name: a statement that speaks of a call of it.
  */
object MemberName:
  /** The member's declarer, name and signature, as the tree read has them. */
  def of(using q: Quotes)(s: q.reflect.Symbol): List[String] = Names[q.type](q).member(s)

  private final class Names[Q <: Quotes & Singleton](val q: Q) extends SourceSyms
