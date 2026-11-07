## Attributes

- id: WI-20260902-40KSW-check-bare-ref-s-fall-through
- created: 2026-09-02T14:18:22Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-07T20:55:39Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`check_bare_ref`'s FALL-THROUGH SAYS "unresolved" ABOUT A NAME THAT RESOLVED, once per segment of a dotted chain.

MEASURED BY ME while delivering WI-20260902-4NEKZ, which closed the ONE row of this
matrix that differed between the two positions and left the other five, since they are
IDENTICAL in both and therefore not a dotted-spelling question:

  chain names        operation body     rule body     (after 4NEKZ)
  a RULE                  1 error          1 error    <- 4NEKZ closed this
  a CONSTRUCTOR           3 errors         3 errors
  a SORT                  2 errors         2 errors
  a NAMESPACE             2 errors         2 errors
  an ENTITY               2 errors         2 errors
  NOTHING                 3 errors         3 errors

  e.g. `rule r(1) :- zzm.Color.red = 7` with `sort Color  entity red  end`:
    9:16: type mismatch in zzm.name:   expected resolved name, got unresolved
    9:16: type mismatch in Color.name: expected resolved name, got unresolved
    9:16: type mismatch in red.name:   expected resolved name, got unresolved

TWO FAULTS, and the second is the one with teeth:

 1. ONE ERROR PER SEGMENT. A single written name produces N diagnostics at ONE span,
    which the author must read as one. `zzm = 7` (a bare NAMESPACE, one segment, no dot)
    produces one, so the cascade is just the chain being walked leaf by leaf.

 2. THE MESSAGE IS FALSE. `zzm`, `zzm.Color` and `zzm.Color.red` all RESOLVE — to a
    namespace, a sort and a constructor. `TypeError::UnresolvedName` renders as "expected
    resolved name, got unresolved", and it is `check_bare_ref`'s FALL-THROUGH: the rungs
    above it answer for a local, a const, a constructor-with-expected, an eta lift, a
    zero-arg op call, a free-standing entity, a sort IN A `Type` SLOT, a relation, an
    equation functor — and anything else, RESOLVED OR NOT, lands on a message that says
    the name does not resolve. An author told "red does not resolve" about a constructor
    that is right there will look for a typo or a missing import; the truth is that a
    constructor has no VALUE reading in that slot.

    Note the SORT rung is deliberately gated on a `Type` slot (WI-206: "gating on the
    expected type keeps a stray sort name in an ordinary value position the loud
    `UnresolvedName` it is today") — so this fall-through is LOAD-BEARING for the sort
    case and cannot simply be deleted; what it needs is to distinguish "no such name" from
    "this name has no value reading here".

ACCEPTANCE: a resolved name with no value reading in the slot is reported ONCE per
written name, with a message that says what the name IS and why it cannot stand there —
never "unresolved". A chain naming NOTHING is still reported once, and still says so.
CONTROLS: a genuinely absent name must keep a diagnosis an author can act on (WI-1034's
"names nothing" census and repair); the SORT-in-a-`Type`-slot rung must keep answering
(WI-206); 4NEKZ's rule row must stay at one `eq.b (op-arg)` error; and the OPERATION BODY
and the RULE BODY must move TOGETHER — they agree today at every one of these five rows,
and a fix applied at one position only would re-open the split 4NEKZ just closed.

## Changes

### 2026-10-12T11:18:08Z — feedback — claude

THE MATRIX MOVED WITH WI-20261012-RXT6S (2026-10-12, 4f282c2a): a chain that names a SORT or a free-standing ENTITY is that name's type value in an OPERATION body now, so `zz4nf.Color = 7` and `zz4nf.acct = 7` there draw one true refusal, 'eq.b (op-arg): expected Type, got Int64', and a CONSTRUCTOR past a sort, `zz4nf.Color.red = 7`, draws one about `red` where it drew three. The RULE body column is unchanged (3, 2, 2), and the NAMESPACE and NOTHING rows are unchanged in both. `wi_4nekz_dotted_equation_operand_test::the_five_other_name_kinds_still_agree_with_the_operation_body` pairs the two bodies for those two rows only. ONE MORE NAME THAT RESOLVES AND IS CALLED UNRESOLVED: an `internal` sort named by a path from another namespace — over `sort Hid { internal sort Sec … }` in `probe`, `nm(probe.Hid.Sec)` in namespace `user` says 'Sec.name: expected resolved name, got unresolved', where `import probe.Hid.Sec`, the parameter type `x: probe.Hid.Sec` and the bracket entry `Bx[V = probe.Hid.Sec]` say ''probe.Hid.Sec' is internal to 'probe.Hid' and cannot be referenced from scope …'. The ladder's rungs read the whole name under visibility (`Loader::resolve_qualified_readonly`), so a hidden const by a path is reported the same way; the companion call `probe.Hid.Sec.sx()` answers.

### 2026-11-07T20:55:35Z — feedback — claude

DELIVERED 2026-11-07. Re-measured on a3082618 first: the rule, constructor, sort and entity rows had closed already (4NEKZ, RXT6S, 9WVT7, QK77S); a namespace by a path (2 errors), a namespace alone (1), a path naming nothing (3, or 2 when the first segment names nothing) and an internal name by a path (the addendum's probe.Hid.Sec, a hidden const Q.hidden.x) still said 'expected resolved name, got unresolved', identically in both bodies. Now each is one error, the same in a rule body, an operation body, a const value, a constraint, a lambda, a call argument and a fired @[simp] right-hand side: '`zz.inner` is a namespace, and a namespace has no value', '`zz.nosuch.x` names nothing: the namespace `zz` declares no `nosuch`', '`nosuch.x` names nothing: no `nosuch` is visible in scope …' with the WI-1034 repair, and the import's "'Sec' is internal to 'probe.Hid'". Controls kept: a rule, a constructor and a sort by a path keep their one eq.b (op-arg) error; a bare name nothing declares keeps its refusal; a written anthill.reflect.field_access(…) keeps its second argument an argument; a field read off a const in an operation body answers. NOT CHANGED, put to the user: a member missing on a sort prefix (zz.Color.nosuch) and a field read off a value prefix in a rule body (zz.Q.origin.x, after the const-in-a-data-slot refusal) still say unresolved; a @[simp] right-hand side naming nothing or an internal name gets the loader's equation-replacement error beside this one (2 where it was 4).

### 2026-11-07T21:48:56Z — feedback — claude

FOLLOW-UP 2026-11-07 (the user: 'also fix 1 and 2'). (1) Measured on 222ec723 first, wider than reported: in a rule body a member named through a path to its sort (`7 = zz.S.seven`, `..zz.S.seven`, the alias path `zz.CA.zero`) was refused 'seven … unresolved' while `S.seven` answered — the walk records the sort a path names as its type value and the chain's name reader took only a reference as its first segment; now read as the one-segment spelling, the alias's bracket handed to the operation as its receiver's type. A member a sort does not declare is refused about the sort, once, in both bodies (`zz.Color.nosuch`, `zz.P.x`), after the alias and provision rungs are asked; the rest of a path past a provided member is read off it (`Int64.compare.x`). A path whose prefix names a value is read as the dot on that value, member by member, in both bodies: `3 = zz.S.mk.x` holds and `4 = …` fails in a rule body, `zz.S.mk.z` is refused naming no member z, `zz.Color.blue.n` is one error in an operation body. A value place (a field, a parameter) is passed over by the walk. An internal name by a path is refused before any reading (the widened reading had let `?v = zz.Q.sec` load), named by its qualified name as the import names it. (2) An equation whose replacement the loader refused is not fired by the typer, which reported the text again at each call (a compound `nosuchfn(?x)` was doubled on 222ec723 too); the loader's outer node leaves a hidden prefix to the inner one, so `zz.Q.hidden.x` in a replacement or a fact argument is one refusal. NOT CHANGED, seen on the way and the same on 222ec723: a `<=>` operand and a goal argument accept a path that names nothing, a namespace, or an internal name (`?v <=> zz.Q.sec` loads); in a rule body `?v <=> zz.S.mk.x` binds the chain as data rather than 3 (proposal 068's evaluation); a path through an alias is printed with the alias expanded (`zz.Box.nosuch` for `zz.CA.nosuch`).

