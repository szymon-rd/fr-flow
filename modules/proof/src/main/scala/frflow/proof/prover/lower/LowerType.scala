package frflow.proof.prover.lower

import frflow.core.ty.Ty
import frflow.proof.prover.ast.*

/** A type as the prover is given it (`(List Grant)`, `(String → Option UserId)`), written into any syntax: every
  * compound type in parentheses. A declaration's type is its parameters' types and its result's, joined by `→`.
  */
class LowerType[E](syntax: Syntax[E]):
  private val atoms = new Atoms(syntax)
  import atoms.{const, name}
  import syntax.{app, infix, paren}
  private def chain(op: LOp, ts: List[E]): E = ts.reduceRight(infix(op, _, _))

  def apply(t: Ty): E = t match
    case Ty.Bool             => name("Prop")
    case Ty.Num(_)           => name("Int")
    case Ty.Str              => name("String")
    case Ty.Unit             => name("Unit")
    case Ty.MapOf(k, v)      => paren(infix(LOp.Arrow, apply(k), app(name("Option"), List(apply(v)))))
    case Ty.SetOf(a)         => paren(infix(LOp.Arrow, apply(a), name("Prop")))
    case Ty.ListOf(a)        => paren(app(name("List"), List(apply(a))))
    case Ty.OptionOf(a)      => paren(app(name("Option"), List(apply(a))))
    case Ty.EitherOf(e, a)   => paren(app(name("Except"), List(apply(e), apply(a))))
    case Ty.TupleOf(as)      => paren(chain(LOp.Times, as.map(apply)))
    case Ty.FnOf(as, r)      => paren(chain(LOp.Arrow, (as :+ r).map(apply)))
    case Ty.Sort(n)          => const(n.value)
    case Ty.Data(n)          => const(n.value)

  /** A binder's type: a function's arrows unparenthesized at the top (`(expire : CrmStore → Int → CrmStore)`). */
  def binder(t: Ty): E = t match
    case Ty.FnOf(as, r) => declaration(as, apply(r))
    case other          => apply(other)

  /** `A → B → R`: a declaration's type, unparenthesized at the top. */
  def declaration(params: List[Ty], result: E): E = chain(LOp.Arrow, params.map(apply) :+ result)

/** The types of the tree, the form a generated module is kept in. */
object LowerType extends LowerType[LExpr](Tree)
