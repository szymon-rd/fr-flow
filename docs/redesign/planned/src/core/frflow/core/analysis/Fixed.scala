package frflow.core.analysis

import frflow.core.name.{SymbolName, TypeName}
import frflow.core.spec.{Fixing, Statement}

/** A term a definition can fix: an opaque type or a symbol. */
enum Fixed:
  case Sort(name: TypeName)
  case Term(name: SymbolName)

object Fixed:
  /** The terms a statement fixes: a definition's, none for every other kind. */
  def of(s: Statement): List[Fixed] = s match
    case Statement.Definition(fs) => fs.toList.map {
      case Fixing.TypeAs(sort, _) => Sort(sort)
      case Fixing.TermAs(sym, _)  => Term(sym)
    }
    case _ => Nil
