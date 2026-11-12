package frflow.core.threads

/** A unit of code read, laid out as the Rocq file it is printed as: the types of its classes and `obj`; the
  * constructors of `code`, one for each closure the code makes; the globals and casts the definitions mention;
  * the methods of the classes not read; the definitions, each after those it calls; and the type of the
  * capabilities a closure of the caller's holds.
  */
final case class Program(types: List[Decl], closures: List[Ctor], support: List[Decl.Definition],
    externs: List[Section], sections: List[Section], holds: Ty):
  /** Every definition of the file but what each closure runs (`interp`), in the order they are written. */
  def definitions: List[Decl.Definition] =
    types.collect { case d: Decl.Definition => d } ++ support ++ (externs ++ sections).flatMap(_.defs)
