package frflow.proof.lean.ast

/** Where a theorem's statement starts: after its name (`theorem holds : S := by`), or on the next line indented by
  * four (`theorem Database.load_onWorld :\n    S := rfl`), as generated today.
  */
enum Break:
  case SameLine, NextLine
