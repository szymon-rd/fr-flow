package frflow.core

/** The package cycles among a module's main sources: each set of two or more packages naming each other, in turn. */
object Cycles:
  def of(files: List[Source]): List[List[String]] =
    val packages = files.map(_.pkg).toSet
    def owner(r: Ref): Option[String] =
      r.path.split('.').toList.inits.map(_.mkString(".")).find(packages)
    val edges = files.flatMap(f => f.refs.filter(_.module == f.module).flatMap(owner).filter(_ != f.pkg)
      .map(f.pkg -> _)).distinct.groupMap(_._1)(_._2)
    def reaches(from: String): Set[String] =
      LazyList.iterate((Set(from), Set.empty[String])) { (front, seen) =>
        val next = front.flatMap(edges.getOrElse(_, Nil)).diff(seen)
        (next, seen ++ next)
      }.dropWhile(_._1.nonEmpty).head._2
    val reach = packages.toList.map(p => p -> reaches(p)).toMap
    packages.toList.map(p => (reach(p) + p).filter(q => q == p || reach(q)(p))).filter(_.size > 1).distinct
      .map(_.toList.sorted)
