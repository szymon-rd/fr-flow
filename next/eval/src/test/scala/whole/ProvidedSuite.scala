package whole

import frflow.core.analysis.Validate

/** Owner §45 D: a value provided where the code runs, read beside the World, is refused; none of the four ports
  * reads one so (crm's, keycloak's and auth's histories and clock are read beside no world until step 13 models them).
  */
class ProvidedSuite extends munit.FunSuite:
  test("no port reads a provided value beside the World") {
    List(rooms.rooms, auth.knowledge, crm.knowledge, keycloak.knowledge).foreach(kb =>
      assertEquals(Validate.providedBesideWorld(Theories.theory(kb)), Nil, kb.name.value))
  }
