package frflow.api.view.diff

/** One content field that moved (`statement`, `formula`, `vocabulary`, …), as a line diff. */
final case class FieldDiff(field: String, lines: List[DiffLine])
