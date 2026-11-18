package frflow.api.view.vocab

import frflow.core.ty.Field

/** One case of a domain type made of cases, and its fields. */
final case class Case(name: String, fields: List[Field])
