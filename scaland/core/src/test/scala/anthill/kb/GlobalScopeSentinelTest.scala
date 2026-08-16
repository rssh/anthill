package anthill.kb

import anthill.intern.GLOBAL_SCOPE_NAME
import anthill.parse.Parser

/** WI-987 — THE SYNTHETIC TOP-LEVEL SCOPE IS NAMED BY A SPELLING NO DECLARATION CAN
  * TAKE. Its spelling used to be `_global`, which both identifier grammars admit
  * (`tree-sitter-anthill/grammar.js`'s `_identifier_token`, `Tokens.identToken` here),
  * so `namespace _global` DEFINED a second scope — `define` writes
  * `byQualifiedName("_global")` and never consults the intern map — and
  * `scopeDisplayName` rendered both of them `_global`. Two live scopes under one name:
  * a WI-962-style diagnostic could not say which one it meant, and a name the author
  * expects at file level resolves against one and not the other.
  *
  * The answer is the one `intern.ABSOLUTE_PATH_MARKER` already takes for the absolute
  * path marker in rustland: a sentinel built out of characters the identifier token
  * does not admit, so the collision is UNREPRESENTABLE rather than merely refused.
  * Angle brackets are this tree's existing spelling for a name no source text can
  * write (`Parser.parse`'s `"<input>"`).
  *
  * CONTROL — put [[anthill.intern.GLOBAL_SCOPE_NAME]] back to `"_global"` and BOTH cases
  * below fail: the first on the rendering inequality (the declaration still makes its
  * own scope — two distinct scopes, one name), the second because `_global` then parses.
  * The two other assertions on the spelling, `ScopeIdentityTest`'s and
  * `PreludeScopesTest`'s, READ the constant, so they move with it rather than
  * discriminating; every remaining test reaches the scope through `kb.globalScope` and
  * never through its text.
  */
class GlobalScopeSentinelTest extends munit.FunSuite:

  test("WI-987: a declared `_global` is a scope of its own, and renders as one") {
    val kb = LoadFixture.loaded(
      """namespace _global
        |  sort S
        |    operation f(x: S) -> S
        |  end
        |end""".stripMargin,
      "<wi987>")

    // The declaration is an ORDINARY namespace — nothing refuses it, and nothing has
    // to: it no longer names what the loader named.
    val declared = kb.symbols.scopeOf(kb.resolveSymbol("_global"))
    assertNotEquals(declared, kb.globalScope)
    assert(kb.hasQualifiedName("_global.S"), "the declared `_global` holds its own members")

    // THE POINT, and the discriminator: two live scopes must not RENDER alike. An
    // inequality and not two equalities against the constant — under the control a pair
    // of equalities BOTH HOLD, measured in the rustland twin, and the case reports green
    // over exactly the defect it exists for.
    assertEquals(kb.scopeDisplayName(declared), "_global")
    assertNotEquals(
      kb.scopeDisplayName(declared),
      kb.scopeDisplayName(kb.globalScope),
      "a diagnostic naming a scope could not say which of the two it meant")
  }

  test("WI-987: the sentinel is unspellable, so a second scope cannot take it") {
    // `identToken` is `[a-zA-Z_][a-zA-Z0-9_-]*`; `<` starts no identifier, so no
    // declaration reaches `define` with this qualified name. Asserted rather than
    // described — this is the whole of why the fix needs no check.
    assert(
      Parser.parse(s"namespace $GLOBAL_SCOPE_NAME\nend", "<wi987>").isLeft,
      "the sentinel must not parse as a namespace name")

    // The LITERAL, pinned once per tree. Rustland's `intern::GLOBAL_SCOPE_NAME` holds
    // the same string and nothing links the two, so each side pins it and a divergence
    // fails on the side that moved rather than in neither.
    assertEquals(GLOBAL_SCOPE_NAME, "<global>")
  }
