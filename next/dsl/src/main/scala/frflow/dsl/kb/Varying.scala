package frflow.dsl.kb

import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{SymbolName, VarId}
import frflow.core.vocab.ValueKind
import frflow.dsl.build.Declarations
import frflow.dsl.node.Node
import frflow.dsl.vocab.Stating

/** Which Declarations change with the World (owner §43), read off the FrModel's statements: those a statement reads
  * beside what changes with it (a model's state, a program's run, a define reading state, or another such
  * Declaration), until no statement adds one. Every Declaration may change with the World; one no statement reads so
  * is the same in each world whatever it is, so Lean is given it as a value, not a function of the world. Each
  * statement is read once open for this (`Stating.probing`), then elaborated over the world it holds in.
  */
object Varying:
  def of(nodes: List[Node]): Set[SymbolName] =
    val read = nodes.flatMap(n => n.statement(Stating.probing).run.toOption.flatMap((ds, s) =>
      s.said.map(f => (declarations(ds), readsWorld(f.value)))))
    closure(read.collect { case (ds, true) => ds }.flatten.toSet, read.map(_._1))

  /** Every Declaration a statement mentions beside one that changes, added until none is. */
  private def closure(varying: Set[SymbolName], statements: List[Set[SymbolName]]): Set[SymbolName] =
    val more = varying ++ statements.filter(_.exists(varying)).flatten
    if more == varying then varying else closure(more, statements)

  private def declarations(ds: Declarations): Set[SymbolName] =
    ds.symbols.collect { case (n, ss) if ss.exists(_.kind == ValueKind.Declaration) => n }.toSet

  private def readsWorld(e: Expr): Boolean = Exprs.all(e).exists {
    case Expr.Var(x) => x.id == VarId.world || VarId.isRan(x.id)
    case _           => false
  }
