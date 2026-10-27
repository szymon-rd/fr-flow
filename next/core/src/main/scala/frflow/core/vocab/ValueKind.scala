package frflow.core.vocab

/** The two kinds of values a model names (owner §15). A `Declaration` is abstract: statements say what it is, no
  * code or program calls it, nothing implements it. A `Definition` is what code and programs use, and it must get a
  * meaning: a program or term-API code (proven), plain Scala (tested), or a value given where its code runs. A
  * `define` is a Definition given its meaning on the spot (in the vocabulary's defines, not its symbols).
  */
enum ValueKind:
  case Declaration, Definition
