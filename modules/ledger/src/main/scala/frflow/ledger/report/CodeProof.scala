package frflow
package ledger
package report

import frflow.protocol.*
import io.circe.Codec

/** How a contract's code meets it: proven down to its code (a proven define, and the code running beside it, tested
  * against the define), a define not proven yet, or plain code tested against the contract (not proven).
  */
enum CodeProof derives Codec.AsObject:
  case ProvenDown(define: String, running: Option[String])
  case Define(name: String, status: ObligationStatus, running: Option[String])
  case Tested(report: Option[TestReport])
  /** A boundary's model, with implementations run against it: the project's own (`own`: tested) and outside systems
    * (`outside`: checked; the model stays assumed).
    */
  case Model(own: List[String], outside: List[String], report: Option[TestReport])

object CodeProof:
  /** How a model's implementations are written in its content: the project's own, or an outside system. */
  val Own = "tested: "
  val Outside = "assumed, checked: "

  def of(n: SnapNode): Option[CodeProof] =
    val impl = n.content.text("implementation")
    val running = impl.linesIterator.find(_.startsWith("runs: ")).map(r => Proofs.runningCode(r.stripPrefix("runs: ")))
    val impls = n.content.strs("implementations")
    n.implementationProof match
      case Some(p) if p.status == ObligationStatus.Proven => Some(ProvenDown(p.name, running))
      case Some(p) => Some(Define(p.name, p.status, running))
      case None if impls.nonEmpty =>
        Some(Model(impls.filter(_.startsWith(Own)).map(_.stripPrefix(Own)), impls.filter(_.startsWith(Outside)).map(_.stripPrefix(Outside)), n.tested))
      case None => Option.when(impl.nonEmpty)(Tested(n.tested))

  /** Whether code of the node is tested, not proven: plain code, or code running beside a proven define. */
  def tested(n: SnapNode): Boolean = of(n).exists {
    case Tested(_)              => true
    case ProvenDown(_, running) => running.isDefined
    case Define(_, _, running)  => running.isDefined
    case Model(own, _, _)       => own.nonEmpty
  }

  /** Whether some code of the node is run against what it is decided to do: tested, or an outside system checked. */
  def run(n: SnapNode): Boolean = tested(n) || of(n).exists { case Model(_, outside, _) => outside.nonEmpty; case _ => false }
