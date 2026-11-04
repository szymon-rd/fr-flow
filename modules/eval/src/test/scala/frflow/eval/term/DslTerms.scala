package frflow.eval.term

import cats.syntax.all.*
import frflow.core.spec.Form
import frflow.core.term.Final
import frflow.core.ty.DataType
import frflow.dsl.build.Declarations
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{LowerEnv, LowerType, Naming}
import frflow.proof.lean.term.Printed

/** The DSL's generated terms (`Generated`: a match over an enum, a record made and updated, defines called by name,
  * `allDistinct`, strings) for the Lean law, with what they declare as Lean: their types and their defines.
  */
object DslTerms:
  val terms: List[Final[Boolean]] = (1L to 150L).toList.map(seed => Generated.formula(seed, 3).run)
  private val declared: Declarations = (1L to 150L).toList.foldMap(seed => Generated.formula(seed, 3).notes.declares)

  /** The domain types the terms declare. */
  val types: List[DataType] = declared.types.values.flatMap(_.headOption).map(_.data).toList.sortBy(_.typeName.value)

  /** Each type as Lean declares it, then each define, printed once as its `def`. */
  def decls(env: LowerEnv, naming: Naming): List[Decl] = types.map(typeDecl) ++ declared.defines.toList
    .sortBy(_._1.value).flatMap((name, ds) => ds.headOption.flatMap(_.run.toOption).map(_._2).flatMap(w =>
      w.form match
        case Form.Term(t)  =>
          val (bs, body) = Printed.define(env, naming)(w.value.params, t.run)
          Some(Decl.Def(List(Attr.FrflowDefs), Names.builtin(name.value), bs, LowerType(w.value.result), body))
        case Form.Steps(_) => None))

  private def typeDecl(d: DataType): Decl = d match
    case DataType.Product(n, _, fs) =>
      Decl.Structure(Names.ident(n.value), fs.map(f => Names.ident(f.name) -> LowerType(f.ty)))
    case DataType.Sum(n, _, cs)     => Decl.Inductive(Names.ident(n.value), cs.toList.map(c =>
      Names.ident(c.name.value) -> c.fields.map(f => LBinder.Explicit(Names.ident(f.name), LowerType(f.ty)))))
