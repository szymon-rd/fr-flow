package frflow.code

// Code a statement speaks of, as a developer writes it: a class with a method that takes an object and data, one
// that takes code, a constructor, and a function of the package.

final class Till(val name: String):
  private val drawer: Item = Item(false)
  private var rings: Int = 0
  def count(): Int = { rings += 1; if drawer.priced then rings else 0 }
  def ring(item: Item, times: Int): Boolean = times > 0 && item.priced
  def each(run: Item => Unit): Unit = run(Item(true))
  def open(): Unit = ()

final class Item(val priced: Boolean)

def closeAll(till: Till, force: Boolean)(using manager: Till): Int =
  if force then till.name.length else manager.name.length
