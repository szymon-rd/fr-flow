package frflow.api.view.vocab

import frflow.core.ty.Field

/** What a domain type is made of: nothing known but what it means (opaque), fields, or cases. */
enum Shape:
  case Opaque(means: String)
  case Record(fields: List[Field])
  case Choice(cases: List[Case])
