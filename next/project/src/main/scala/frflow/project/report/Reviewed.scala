package frflow.project.report

import frflow.core.name.NodeId
import frflow.decision.review.{Mechanical, Standing, Subject}

/** One node as the review reads it: the subject, its standing (state and causes), the first node it waits for, and
  * why a batch (`confirm`) would not take it, if it would not.
  */
final case class Reviewed(subject: Subject, standing: Standing, waitsFor: Option[NodeId],
    notMechanical: Option[Mechanical.Not])
