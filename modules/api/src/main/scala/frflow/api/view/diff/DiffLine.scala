package frflow.api.view.diff

/** A line of a diff: kept, added or removed. Folding long unchanged runs is the front end's. */
enum DiffLine:
  case Same(text: String)
  case Added(text: String)
  case Removed(text: String)
