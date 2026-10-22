package crm

/** The running write side: the registered implementation, every new store checked against
  * WriteContract. WriteSideWiring governs this file, so a change to it is the developer's to review.
  */
def writeSide(): (CrmStore, WriteCmd) => CrmStore =
  knowledge.service(writeContract)()
