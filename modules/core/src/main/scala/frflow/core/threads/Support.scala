package frflow.core.threads

/** What the definitions read may mention beside each other and the library; a file holds those it does mention.
  *
  *   - `shared`: the cases of `obj` a caller's data may hold whatever the code does (a public class read);
  *   - `held`: the cases of `obj` for what the code itself puts where a `val` is;
  *   - `globals`: a top-level value that holds an object of the JDK, or one of a class not read: a fixed handle;
  *   - `casts`: a value read at a type from where it is held as a `val`, a sum read as one of its cases, a test
  *     that a `val` is a given object;
  *   - `externs`: for each class not read, its methods, each a definition that is `extern`.
  */
final case class Support(shared: List[Ctor], held: List[Ctor], globals: List[Decl.Definition],
    casts: List[Decl.Definition], externs: List[Section])
