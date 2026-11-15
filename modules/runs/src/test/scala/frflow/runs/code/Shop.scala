package frflow.runs.code

// Code a statement speaks of, as a developer writes it: a class with a method that takes an object and data, one
// that takes code, a constructor, and a function of the package.

final class Till(val name: String):
  def ring(item: Item, times: Int): Boolean = times > 0 && item.priced
  def each(run: Item => Unit): Unit = run(Item(true))
  def open(): Unit = ()

final class Item(val priced: Boolean)

def closeAll(till: Till, force: Boolean)(using manager: Till): Int =
  if force then till.name.length else manager.name.length
