package frflow
package boundary

final class State[S] private[frflow] (model: StateModel[S]):
  def get: Flow[S] = Flow.Get(model)
  def set(s: Term[S]): Flow[Unit] = Flow.Put(model, s)
  def update(f: Term[S] => Term[S]): Flow[Unit] = Flow.Update(model, f)
