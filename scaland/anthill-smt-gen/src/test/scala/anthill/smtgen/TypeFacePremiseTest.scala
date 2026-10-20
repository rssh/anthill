package anthill.smtgen

/** WI-20261020-80VNX (rustland's `is_known_entity` face guard, WI-20260902-JB6RS step 2) —
  * A PREMISE WRITTEN WITH THE BRACKET IS A TYPE, NOT AN ENTITY DESTRUCTURE. `Params[base =
  * ?b]` is headed by `Params`'s TYPE FACE, which reads the declaration's field schema (a
  * face answers what its declaration answers) — so without the guard `isKnownEntity`
  * took it for the instance pattern `Params(base: ?b)` and encoded `?b` as the field, a
  * premise the rule does not state.
  *
  * BACKED OUT (`isKnownEntity` without its `!sym.isTypeFace`): `citesType` emits a
  * document carrying `base`. `citesInstance` emits either way BY DESIGN — the control that
  * the entity premise itself is encoded. */
class TypeFacePremiseTest extends munit.FunSuite:

  private def kb = Common.loadKbWith("""
    namespace test.smt.face
      import anthill.prelude.{Float}
      import anthill.prelude.Numeric.{add}

      entity Params(base: Float)

      rule citesType(?r) :- Params[base = ?b], ?r = add(?b, 1.0)
      rule citesInstance(?r) :- Params(base: ?b), ?r = add(?b, 1.0)

      fact Params(base: 2.0)
    end
  """)

  test("a type premise is not an entity destructure") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.face.citesType") match
      case Right(doc) => fail(s"`Params[base = ?b]` is a type, not the instance pattern:\n$doc")
      case Left(e) =>
        assert(!e.message.contains("binds no field"), s"refused as a type, not a destructure: ${e.message}")
  }

  test("the instance premise is encoded: the control") {
    SmtGen.emitSatisfiabilityCheck(kb, "test.smt.face.citesInstance") match
      case Right(doc) => assert(doc.contains("base"), s"the field reaches the encoding:\n$doc")
      case Left(e) => fail(s"an entity premise was never broken: ${e.message}")
  }
