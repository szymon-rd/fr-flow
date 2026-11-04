package frflow.api.shell

import frflow.api.view.Stop
import frflow.project.pipeline.Problems
import frflow.project.port.FrFlowError
import frflow.wire.file.Unreadable

/** The shell's errors as the front ends see them (`Stop`); any other error is left as it is. */
private[api] object Stops:
  val of: PartialFunction[Throwable, Throwable] =
    case Problems.Invalid(ps)                   => Stop.Invalid(ps)
    case FrFlowError.NoLean                     => Stop.NoLean
    case FrFlowError.UnknownNode(id)            => Stop.UnknownNode(id)
    case FrFlowError.NotRead(u)                 => unread(u)
    case FrFlowError.NoKey(file)                => Stop.NoKey(file)
    case FrFlowError.NotAKey(file, problem)     => Stop.NotAKey(file, problem)

  private def unread(u: Unreadable): Stop = u match
    case Unreadable.NotJson(f, p)               => Stop.NotJson(f, p)
    case Unreadable.NoVersion(f)                => Stop.NoVersion(f)
    case Unreadable.UnknownVersion(f, v, r)     => Stop.UnknownVersion(f, v, r)
    case Unreadable.BadField(f, v, field, p)    => Stop.BadField(f, v, field, p)
