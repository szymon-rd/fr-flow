package frflow.eval.run

/** What a proven program is to the values code reads: run, through `Running` (production: as a value it is none), or
  * its run on the models (the examples and the generated tests, `ProgramRun`).
  */
enum Programs:
  case Run, OnModels
