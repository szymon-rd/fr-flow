package frflow.api.view.source

/** What of a file a node governs: the file whole, or the definitions its code refers to in a file of the model's. */
enum FilePart:
  case Whole
  case Named(names: List[String])
