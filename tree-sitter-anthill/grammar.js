/// Tree-sitter grammar for the Anthill kernel language.
///
/// The kernel has 4 constructs: namespace, sort, rule, operation.
/// Sugar adds: entity, fact, constraint, operation/rule blocks.
///
/// All keywords except `true`/`false` are soft (context-dependent).
/// See: docs/kernel-language.md

module.exports = grammar({
  name: 'anthill',

  extras: $ => [
    /\s/,
    $.line_comment,
    $.block_comment,
  ],

  word: $ => $._identifier_token,

  reserved: {
    // Only true/false are always reserved
    global: $ => ['true', 'false'],
    // In identifier positions, nothing is reserved
    none: $ => [],
  },

  supertypes: $ => [
    $._declaration,
    $._term,
    $._type,
  ],

  conflicts: $ => [
    // (removed: rule_declaration vs rule_entry and operation_declaration vs
    // operation_entry conflicts — brace-less rule/operation blocks dropped in
    // WI-497, so a block no longer shares a prefix with a single declaration)
    // (removed: abstract_sort vs sort_with_body conflict — `= ?` disambiguates)
    // After operation clauses, `requires` could be another clause or a standalone declaration
    [$.operation_declaration],
    [$.variable_term],
    [$.variable_term, $.fn_term],
    // `p.x` / `?x.m` is field_access; `p.x(...)` / `?x.m(...)` extends it into
    // a fn_term. Explore both branches, pick by whether `(` follows.
    [$._atom_term, $.fn_term],
    // [ after rule head could be meta_block or start of next rule_entry with collection_literal
    [$.rule_entry],
  ],

  rules: {

    // =========================================================
    // Top-level
    // =========================================================

    source_file: $ => repeat($._top_level),

    _top_level: $ => choice(
      $._declaration,
    ),

    // =========================================================
    // Kernel declarations
    // =========================================================

    _declaration: $ => choice(
      $.namespace_declaration,
      $.abstract_sort,
      $.sort_with_body,
      $.sort_var_binder,
      $.sort_bracket_binder,
      $.enum_declaration,
      $.rule_declaration,
      $.operation_declaration,
      $.requires_declaration,
      // Sugar
      $.entity_declaration,
      $.fact_declaration,
      $.constraint_declaration,
      $.operation_block,
      $.rule_block,
      $.describe_declaration,
      // Proof + provides (proposal 025)
      $.proof_declaration,
      $.provides_block,
    ),

    // =========================================================
    // Namespace
    // =========================================================

    namespace_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      'namespace',
      field('name', $.name),
      $._body_namespace,
    ),

    import_clause: $ => seq(
      'import',
      $.import_path,
    ),

    // Dedicated import path rule: a flat sequence of dot-separated segments.
    // The segment type after each '.' determines the import kind:
    //   - all identifiers     → plain import (e.g., import anthill.prelude.List)
    //   - last is {names}     → selective   (e.g., import anthill.prelude.{List, Option})
    //   - last is *           → wildcard    (e.g., import anthill.prelude.*)
    //
    // No ambiguity: '.' is always consumed by the repeat, and the segment
    // after '.' is unambiguously identifier, '*', or '{...}'.
    import_path: $ => seq(
      $.identifier,
      repeat(seq('.', $._import_segment)),
    ),

    _import_segment: $ => choice(
      $.identifier,
      $.wildcard_import,
      $.selective_import,
    ),

    wildcard_import: $ => '*',

    selective_import: $ => seq('{', commaSep1($.identifier), '}'),

    // Sort bindings accept two forms:
    //   - `name = value`      — named binding (`T = Int`, `n = 3`)
    //   - any common-type-expr — positional (`Function[Int, Int]`,
    //     `Function[(Int, Int), Int]`, `Effect{?r}` via variable_term, `3`)
    // The binding value is a `_common_type_expr` (see below), not a bare
    // `_type`: a type-argument slot may hold a value (constant, or a value
    // standing in a type position). The loader classifies name/projection
    // values as `denoted` vs `sort_ref` via scope+SymbolKind (WI-302).
    sort_binding: $ => choice(
      seq(field('param', $.name), '=', field('type', $._common_type_expr)),
      field('type', $._common_type_expr),
    ),

    // commonTypeExpr: what may appear as a type argument.
    //   - `_type`        — the type forms (names, applications, tuples,
    //                      arrows, variables); covers names/projections that
    //                      stand for values too (loader decides via SymbolKind).
    //   - literals       — a constant standing in a type position
    //                      (`Vector[Int, 3]`, `Fin[8]`); always a value.
    // Literals are unambiguous here (no `_type` form derives a literal), so
    // this widening is conflict-free. Calls (`Modify[f(x)]`) are reduce-tier
    // and deferred until the typer has a reduction hook.
    _common_type_expr: $ => choice(
      $._type,
      $.integer_literal,
      $.float_literal,
      $.string_literal,
      $.boolean_literal,
      // WI-375: a WRITTEN effect-row in a type-argument value slot —
      // `Stream[E = {}]` / `Stream[E = {Modify[c]}]`. `{`-prefixed ⇒ disjoint
      // from every `_type`, so admitting it here is conflict-free.
      $.effect_row,
    ),

    // WI-375 (proposal 045 §2): a braced effect-row written in the
    // `sort_binding` value slot. A NAMED node (not an inline `seq`) so the
    // converter can recognize the braces — an inline alternative drops them in
    // the CST, conflating `{X}` with `X` and the empty `{}` with a missing
    // value. The empty row `{}` is included (`commaSep`, not `commaSep1`). The
    // loader classifies row-vs-set-literal by the bound param's kind; only the
    // effect-row use is wired (the effect-SET-as-type-argument is unbuilt).
    effect_row: $ => seq('{', commaSep($._effect_type), '}'),

    _body_namespace: $ => choice(
      seq('{', repeat($._namespace_content), '}'),
      seq(repeat($._namespace_content), 'end', optional($.name)),
    ),

    _namespace_content: $ => choice(
      $.namespace_declaration,
      $.abstract_sort,
      $.sort_with_body,
      $.sort_var_binder,
      $.sort_bracket_binder,
      $.enum_declaration,
      $.rule_declaration,
      $.operation_declaration,
      $.requires_declaration,
      $.entity_declaration,
      $.fact_declaration,
      $.constraint_declaration,
      $.operation_block,
      $.rule_block,
      $.describe_declaration,
      $.import_clause,
      $.proof_declaration,
      $.provides_block,
    ),

    _body_sort: $ => choice(
      seq('{', repeat($._sort_content), '}'),
      seq(repeat($._sort_content), 'end', optional($.name)),
    ),

    _sort_content: $ => choice(
      $.namespace_declaration,
      $.abstract_sort,
      $.sort_with_body,
      $.sort_var_binder,
      $.sort_bracket_binder,
      $.effects_sort_item,
      $.enum_declaration,
      $.rule_declaration,
      $.operation_declaration,
      $.requires_declaration,
      $.entity_declaration,
      $.fact_declaration,
      $.constraint_declaration,
      $.operation_block,
      $.rule_block,
      $.describe_declaration,
      $.import_clause,
      $.proof_declaration,
      $.provides_clause,
    ),

    // =========================================================
    // Sort (abstract and defined)
    // =========================================================

    abstract_sort: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'sort',
      field('name', $.name),
      '=',
      field('definition', $._type),
      optional($.meta_block),
    ),

    sort_with_body: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'sort',
      field('name', $.name),
      // WI-451 (§5.4): operation-style enclosing type-param list AFTER the name
      // — `sort CpsMonad[F[T]]`. Each param is a NON-RIGID type variable; a
      // higher-kinded param carries its own bracketed member (`F[T]`). Like an
      // `operation_type_param_list` in position, but a param may be HK (`F[T]`),
      // which that flat list cannot express. Convert desugars it into marked
      // body items.
      optional($.sort_type_param_list),
      $._body_sort,
      optional($.meta_block),
    ),

    // WI-451 (§5.4 non-rigid type-variable marker). A sort's type-parameter
    // binders, after the name, op-style: `[F[T], A, B]`. A param is either SIMPLE
    // (`A`, desugars to `sort A = ?`) or HIGHER-KINDED (`F[T]`, a binder that
    // itself carries a bracketed member — the one shape the flat
    // `operation_type_param_list` lacks). Recursive: the member list reuses this
    // rule. No `= default` form — sort-param defaults are undefined by §5.4 (the
    // examples are bare `[F[T]]` / `[A, B]`); a defaulted sort is the `sort X = T`
    // body form.
    sort_type_param_list: $ => seq(
      '[',
      commaSep1($.sort_type_param),
      ']',
    ),

    sort_type_param: $ => seq(
      field('name', $.identifier),
      optional($.sort_type_param_list),
    ),

    // WI-454 (§5.4 surface sugar): PER-STATEMENT non-rigid type-variable binder
    // synonyms of the WI-451 enclosing-list param. `sort ?X` reuses the `?x`
    // logical-var marker as the binder name; `sort [X]` is the standalone bracket
    // binder. Both fit NEITHER `abstract_sort` (needs `= type`) NOR
    // `sort_with_body` (needs a body AND a plain `name`, not a `?`-marker / a
    // leading `[`), so they get their own productions. The token after `sort`
    // disambiguates: a plain `name` → abstract_sort / sort_with_body, a `variable`
    // (`?X`) → here, a leading `[` → the bracket binder. A structured binder
    // carries members in a BRACE body (`sort ?F { sort ?T }` / `sort [F] { sort
    // [T] }`) — brace-only on purpose: an optional `end`-form body would create a
    // dangling-`end` ambiguity (bare binder + parent `end` vs an empty own body).
    // Convert desugars all four to the SAME IR the enclosing-list form produces.
    sort_var_binder: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'sort',
      field('marker', $.variable),
      optional($.sort_binder_body),
      optional($.meta_block),
    ),

    sort_bracket_binder: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'sort',
      '[',
      field('name', $.identifier),
      ']',
      optional($.sort_binder_body),
      optional($.meta_block),
    ),

    // A structured binder's members are themselves type-variable binders ONLY
    // (`sort ?T` / `sort [T]`, possibly nested HK) — exactly mirroring the enclosing
    // HK member list `F[T, …]` (`sort_type_param_list = [ commaSep1(sort_type_param) ]`).
    // `repeat1` (not `repeat`) so an empty `sort [F] {}` is a loud parse error rather
    // than a degenerate zero-member HK carrier; admitting arbitrary `_sort_content`
    // (ops / entities / facts) would let a type parameter silently carry real
    // declarations the enclosing form cannot express.
    sort_binder_body: $ => seq(
      '{',
      repeat1(choice($.sort_var_binder, $.sort_bracket_binder)),
      '}',
    ),

    // WI-320 / proposal 045: effects-keyword sugar for an effect-row
    // variable at sort-item position. Mandatory `=` form:
    //   - `effects E = ?`    (explicit `?`)  — anonymous row variable
    //   - `effects E = X`    (bound)         — row variable bound to X
    //
    // Desugars at convert time to the pair
    //   `sort E = ?` (or `= X`)  +  `requires EffectsRuntime[Effects = E]`
    //
    // The `=` is mandatory to disambiguate from `effects_clause` (an
    // operation-clause variant) — both productions can begin `effects E`,
    // and a bare-form `effects_sort_item` collides with `effects_clause`
    // inside `operation_declaration`'s `repeat($.operation_clause)`. With
    // `=` required, the two productions are unambiguous at every position.
    // The cost: migration sites write `effects E = ?` rather than
    // `effects E` — a few extra characters, fully explicit about the row
    // variable's `?` kind.
    effects_sort_item: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'effects',
      field('name', $.name),
      '=',
      field('definition', $._type),
      optional($.meta_block),
    ),

    enum_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'enum',
      field('name', $.name),
      $._body_enum,
      optional($.meta_block),
    ),

    _body_enum: $ => choice(
      seq('{', repeat($._enum_content), '}'),
      seq(repeat($._enum_content), 'end', optional($.name)),
    ),

    _enum_content: $ => choice(
      $.abstract_sort,
      $.effects_sort_item,
      $.requires_declaration,
      $.entity_declaration,
      $.operation_declaration,
      $.operation_block,
      $.fact_declaration,
      $.constraint_declaration,
      $.rule_declaration,
      $.rule_block,
      $.describe_declaration,
      $.import_clause,
      $.proof_declaration,
      $.provides_clause,
    ),

    constructor: $ => seq(
      'entity',
      field('name', $.name),
      optional(seq('(', commaSep1($.field_decl), ')')),
    ),

    field_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $._type),
    ),

    // =========================================================
    // Rule
    // =========================================================

    // A rule has body (premises after `:-`) and optional conclusion
    // (after `-:`). Without `-:`, the rule is "violation-shape" —
    // a refutation target whose body must be unsat for the proof to
    // discharge. With `-:`, the rule is a positive theorem of the
    // form `∀ vars. premises ⇒ conclusion`. Z3 discharge negates the
    // conclusion (`assert (not (and conclusion)); check-sat`); the
    // `using` clause's lift step emits the implication directly.
    //
    // The two arrows `:-` and `-:` are mirror surface forms of the same
    // implication operator (see proposal 032). Exactly one of them
    // appears per rule (or neither, for a fact); the dual-arrow form
    // `head :- body -: conclusion` no longer exists.
    //
    // Heads are comma-separated for conjunctive multi-head sugar:
    // `H1, H2 :- B` desugars at load time to two Horn rules sharing
    // body B. `⊥` may appear only as a sole head (denial); it cannot
    // be mixed with positive heads.
    rule_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      'rule',
      optional(seq(field('label', $.name), ':')),
      choice(
        seq(field('heads', $.rule_heads), ':-', field('body', $.rule_body)),
        seq(field('body', $.rule_body), '-:', field('heads', $.rule_heads)),
        field('heads', $.rule_heads),
      ),
      optional($.meta_block),
    ),

    rule_heads: $ => choice(
      '⊥',
      commaSep1($._term),
    ),

    rule_body: $ => commaSep1($._term),

    // =========================================================
    // Operation
    // =========================================================

    operation_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'operation',
      field('name', $.name),
      optional($.operation_type_param_list),
      '(',
      optional(commaSep1($.param)),
      ')',
      '->',
      field('return_type', $._type),
      repeat($.operation_clause),
      optional(seq('=', choice(
        seq('{', field('body', $._expr_body), '}'),
        field('body', $._expr_body),
      ))),
      optional($.meta_block),
    ),

    // Distinct CST node from `sort_binding` even though tokens coincide —
    // this declares operation-local logical variables, not bindings of
    // sort parameters at an instantiation site.
    operation_type_param_list: $ => seq(
      '[',
      commaSep1($.operation_type_param),
      ']',
    ),

    operation_type_param: $ => seq(
      field('name', $.identifier),
      optional(seq('=', field('default', $._type))),
    ),

    param: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $._type),
    ),

    operation_clause: $ => choice(
      $.requires_clause,
      $.ensures_clause,
      $.effects_clause,
      $.meta_clause,
    ),

    // WI-087: operation attributes / metadata. A keyword-introduced clause
    // carrying the existing `meta_block` (`[Marker, Key: value, ...]`). The
    // `meta` keyword is the disambiguating vehicle: a bare `[...]` placed right
    // after the return type is otherwise grabbed as return-type application args
    // (`-> Vec3[...]`), which fails for clauseless ops (pure getter bindings —
    // exactly the ones that carry codegen markers). As a clause it composes with
    // effects / requires / ensures and works with no other clause present.
    meta_clause: $ => seq('meta', $.meta_block),

    requires_declaration: $ => seq(
      'requires',
      field('type', $._type),
    ),

    // WI-448: a trailing `requires` after an operation's return type is the
    // operation's clause (op-scoped), NOT a standalone `requires_declaration`
    // (which is sort/namespace-scoped). Both begin with the `requires` token,
    // so the GLR conflict `[$.operation_declaration]` (above) explores both
    // parses. Their costs are otherwise equal, and a comment (line or block)
    // preceding the operation tips the tie toward the standalone declaration —
    // silently re-scoping the clause's names (e.g. op-type-params) to the
    // enclosing namespace. `prec.dynamic` breaks the tie deterministically
    // toward the op-clause, matching the comment-free behavior regardless of
    // any preceding comment.
    // (`ensures` has no standalone form, so it needs no bias.)
    requires_clause: $ => prec.dynamic(1, seq('requires', $.rule_body)),
    ensures_clause: $ => seq('ensures', $.rule_body),
    effects_clause: $ => seq('effects', $._effect_set),

    // Effect set — single effect type or braced list. Shared between
    // `effects_clause` (operation declarations) and the arrow-type
    // `@` annotation.
    //
    // The single-effect form rejects type variants that begin with `(`
    // (tuple_type, arrow_type) — neither is meaningful as an effect.
    // Accepting them would let a malformed clause like
    // `effects (Modify self)` (a common typo for `Modify[self]`)
    // consume the `(` as the start of an arrow/tuple type and cascade
    // error recovery across the enclosing sort body. With `(` rejected
    // up-front the parser fails at the bad token and resyncs at the
    // next clause keyword.
    // WI-440: `commaSep` (not `commaSep1`) so the explicit closed-empty row
    // `{}` parses — previously `@ {}` failed the braced form and error-
    // recovered into a zero-width `simple_type` (an empty-name unresolved-
    // symbol warning downstream, with the annotation silently dropped).
    _effect_set: $ => choice(
      $._effect_type,                                   // single: E
      seq('{', commaSep($._effect_type), '}'),          // braced: {A, B} / {}
    ),

    // WI-327: extended `_effect_type` admits the proposal-045 surface
    // algebra — explicit `+E` presence, `-E` absence (lacks-constraint,
    // v1b consumer), and `merge(E1, …, En)` union (sugar for the braced
    // set form, allowing nested effect-expressions).
    _effect_type: $ => choice(
      $.simple_type,
      $.application,
      $.variable_term,
      $.effect_presence,
      $.effect_absence,
      $.effect_merge,
    ),

    // `+E` — explicit presence. Sugar; the bare `E` form already defaults
    // to presence. Allowed on a simple effect (not on `merge(...)` —
    // doesn't compose meaningfully).
    effect_presence: $ => seq('+', field('effect', $._simple_effect)),

    // `-E` — absence / lacks-constraint. v1a parses + lowers to
    // `absent(E)`; v1b consumes via [`unify_effect_rows`]' `_a_absent`
    // slot.
    effect_absence: $ => seq('-', field('effect', $._simple_effect)),

    // `merge(E1, …, En)` — union of effect expressions. Lowers
    // identically to the braced-set form `{E1, …, En}` (each element
    // canonicalized into the same `effects_rows` merge chain). Allows
    // nesting (e.g. `merge(+A, -B, rho)`).
    effect_merge: $ => seq(
      'merge',
      '(',
      commaSep1(field('effect', $._effect_type)),
      ')',
    ),

    // Simple effect — without the WI-327 composite forms. Used as the
    // RHS of `+` and `-` (the prefix operators don't recurse into
    // composite forms; `+merge(…)` is ill-formed).
    _simple_effect: $ => choice(
      $.simple_type,
      $.application,
      $.variable_term,
    ),

    // =========================================================
    // Sugar: entity, fact, constraint
    // =========================================================

    entity_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      optional($.visibility),
      'entity',
      field('name', $.name),
      optional(seq('(', commaSep1($.field_decl), ')')),
      optional($.meta_block),
    ),

    fact_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      'fact',
      field('term', $._term),
      optional($.meta_block),
    ),

    constraint_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      'constraint',
      optional(seq(field('label', $.name), ':')),
      field('head', $._constraint_body),
      optional($.meta_block),
    ),

    _constraint_body: $ => choice(
      $.quantified_constraint,
      $.aggregation_constraint,
      seq($.rule_body, optional(choice(
        seq(':-', field('guard', $.rule_body)),
        seq('-:', field('conclusion', $.rule_body)),
      ))),
    ),

    quantified_constraint: $ => prec.right(seq(
      field('quantifier', $.quantifier_keyword),
      choice(
        // Typed binding: forall (?x: T) -: body
        // Sugar for: forall ?x: TypeOf(occ: ?x, type: T) -: body
        seq(field('typed_binding', $.typed_constraint_binding), '-:', field('body', $._constraint_body)),
        // Explicit condition: forall ?x: condition -: body
        seq(field('var', $.variable), ':', field('condition', $.rule_body), '-:', field('body', $._constraint_body)),
        // Bare variable (condition is the body itself): forall ?x -: body
        seq(field('var', $.variable), '-:', field('body', $._constraint_body)),
      ),
    )),

    typed_constraint_binding: $ => seq(
      '(',
      field('var', $.variable),
      ':',
      field('type', $._term),
      ')',
    ),

    quantifier_keyword: $ => choice('forall', 'some', 'one', 'lone', 'no'),

    aggregation_constraint: $ => seq(
      field('aggregate', $.aggregate_keyword),
      '(',
      field('var', $.variable),
      ':',
      field('condition', $.rule_body),
      '-:',
      field('body', $.rule_body),
      ')',
      field('op', $.comparison_op),
      field('bound', $._term),
    ),

    aggregate_keyword: $ => choice('count', 'sum', 'min', 'max'),

    comparison_op: $ => choice('<=', '>=', '<', '>', '=', '!='),

    // =========================================================
    // Description blocks
    // =========================================================

    description_block: $ => token(seq('{<', /[^>]*(?:>[^}][^>]*)*/, '>}')),

    describe_declaration: $ => prec.right(seq(
      'describe',
      field('target', $.name),
      repeat1(field('content', $.description_block)),
    )),

    // =========================================================
    // Proof construct (proposal 025)
    // =========================================================
    //
    // proof <rule-name>
    //   by derivation                     -- kernel SLD search
    //   by z3(timeout: 5000, logic: "LRA") -- external solver
    //   by test(runs: 1000)               -- test runner
    //   query "(assert ...)"              -- explicit external query
    //     mapping { add -> +, eq -> = }
    //   :- hint1, hint2                   -- guided derivation hints
    // end

    // Two body shapes:
    //
    //   * Single-tactic: `proof X [using Y...] by <tactic> [body] end`
    //     — one tactic discharges the whole rule.
    //   * Structured (proposal 031): `proof X (rule h_i: ... by t_i)+
    //     [using ... by t] end` — sequence of step rules followed by an
    //     optional concluding `using ... by ...` clause that discharges
    //     the enclosing lemma's head under accumulated hypotheses.
    proof_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      'proof',
      field('target', $.name),
      choice(
        seq(
          optional(seq('using', field('using', $.proof_using_list))),
          optional(seq('by', field('strategy', $.proof_strategy))),
          optional($._proof_body),
        ),
        seq(
          repeat1(field('step', $.proof_step)),
          optional(field('conclude', $.proof_concluding_clause)),
        ),
      ),
      'end',
      optional($.name),
    ),

    // A step inside a structured proof body. Same shape as a top-level
    // rule_declaration (single-arrow per proposal 032) plus optional
    // `using` and a mandatory `by <tactic>`.
    proof_step: $ => seq(
      'rule',
      optional(seq(field('label', $.name), ':')),
      choice(
        seq(field('heads', $.rule_heads), ':-', field('body', $.rule_body)),
        seq(field('body', $.rule_body), '-:', field('heads', $.rule_heads)),
        field('heads', $.rule_heads),
      ),
      optional($.meta_block),
      optional(seq('using', field('using', $.proof_using_list))),
      'by',
      field('tactic', $.proof_strategy),
    ),

    // The trailing `[using ...] by <tactic>` clause that discharges the
    // enclosing lemma's head under accumulated step hypotheses.
    proof_concluding_clause: $ => seq(
      optional(seq('using', field('using', $.proof_using_list))),
      'by',
      field('tactic', $.proof_strategy),
    ),

    // Comma-separated list of previously-proved lemma names that the
    // prove driver should cite as hypotheses when discharging this
    // proof. Each name resolves to a rule QN; smt-gen renders the
    // cited rule's body and splices it into the SMT preamble as
    // `(assert …)` clauses (via `ProofConfig.assumptions`).
    //
    //   proof safety_min_distance
    //     using reachability_band, distance_at_step
    //     by z3(logic: "QF_NRA")
    //   end
    proof_using_list: $ => seq(
      $.name,
      repeat(seq(',', $.name)),
    ),

    proof_strategy: $ => choice(
      field('name', $.identifier),
      seq(field('name', $.identifier), '(', commaSep1($._fn_arg), ')'),
    ),

    _proof_body: $ => choice(
      seq(':-', field('hints', $.rule_body)),
      seq(
        'query', field('query', $.string_literal),
        optional(seq('mapping', field('mapping', $.mapping_block))),
      ),
    ),

    mapping_block: $ => seq(
      '{',
      commaSep1($.mapping_entry),
      optional(','),
      '}',
    ),

    // mapping rhs is a free string token (e.g. `+`, `=`, `Int`) — to keep
    // it simple we accept either a name or a string_literal.
    mapping_entry: $ => seq(
      field('source', $.name),
      '->',
      field('target', choice($.name, $.string_literal)),
    ),

    // =========================================================
    // Provides construct (proposal 025)
    // =========================================================
    //
    // Inside a sort body — declares spec satisfaction:
    //   provides Stack[T = Int]
    //
    // Standalone block — delivers work:
    //   provides Stack[T = Int]
    //     language anthill
    //     rule push(?s, ?x) = cons(head: ?x, tail: ?s)
    //     proof push_pop by derivation end
    //   end
    //
    //   provides Stack[T = Int]
    //     language rust
    //     artifact "src/stack.rs"
    //     carrier { T: i64 }
    //     namespace_map { Stack: "crate::stack" }
    //   end

    provides_clause: $ => seq(
      'provides',
      field('spec', $._type),
    ),

    provides_block: $ => seq(
      repeat(field('description', $.description_block)),
      'provides',
      field('spec', $._type),
      'language', field('language', $.identifier),
      repeat($._provides_content),
      'end',
      optional($.name),
    ),

    _provides_content: $ => choice(
      $.rule_declaration,
      $.proof_declaration,
      $.fact_declaration,
      $.rule_block,
      $.artifact_clause,
      $.carrier_clause,
      $.namespace_map_clause,
    ),

    artifact_clause: $ => seq('artifact', field('path', $.string_literal)),
    carrier_clause: $ => seq('carrier', field('bindings', $.bindings)),
    namespace_map_clause: $ => seq('namespace_map', field('bindings', $.bindings)),

    // =========================================================
    // Sugar: operation block, rule block
    // =========================================================

    operation_block: $ => seq(
      'operation',
      '{', repeat($.operation_entry), '}',
    ),

    operation_entry: $ => seq(
      optional($.visibility),
      field('name', $.name),
      optional($.operation_type_param_list),
      '(',
      optional(commaSep1($.param)),
      ')',
      '->',
      field('return_type', $._type),
      repeat($.operation_clause),
      optional(seq('=', choice(
        seq('{', field('body', $._expr_body), '}'),
        field('body', $._expr_body),
      ))),
      optional($.meta_block),
    ),

    rule_block: $ => seq(
      'rule',
      '{', repeat($.rule_entry), '}',
    ),

    rule_entry: $ => seq(
      optional(seq(field('label', $.name), ':')),
      choice(
        seq(field('heads', $.rule_heads), ':-', field('body', $.rule_body)),
        seq(field('body', $.rule_body), '-:', field('heads', $.rule_heads)),
        field('heads', $.rule_heads),
      ),
      optional($.meta_block),
    ),

    // =========================================================
    // Stage 0: project
    // =========================================================

    // =========================================================
    // Metadata
    // =========================================================

    meta_block: $ => seq(
      '[',
      commaSep1($.meta_entry),
      ']',
    ),

    // Open-keyed: any Name optionally followed by `: Term`. Well-known
    // keys (trust, agent, timestamp, iteration, source, supersedes,
    // and the WI-139 rule-attribute flags simp/unfold/hint) have
    // kernel semantics; additional keys are project-defined.
    //
    // Flag form: `[simp]` is shorthand for `[simp: true]` — the
    // converter sees a missing value and defaults to Term::Bottom,
    // and `meta_has_flag` only checks key presence regardless of
    // value, so the two forms are interchangeable for predicate
    // queries.
    meta_entry: $ => seq(
      field('key', $.name),
      optional(seq(':', field('value', $._term))),
    ),

    trust_level: $ => choice(
      'proved',
      'verified',
      $.tested_n,
      'empirical',
      'proposed',
      'stale',
      'axiom',
      'decision',
    ),

    tested_n: $ => /tested-[0-9]+/,

    // =========================================================
    // Visibility
    // =========================================================

    visibility: $ => choice('internal', 'public'),

    // =========================================================
    // Terms
    // =========================================================

    _term: $ => choice(
      $._atom_term,
      $.infix_term,
    ),

    // Atomic terms: everything except infix_term. Used as operands in
    // infix_term and prefix_term to force flat chains.
    // WI-311: the bare-reference atom is `$.name` (was `$.identifier`), so a
    // dotted application base (`scala.prelude.List[Int]`) and a qualified ref
    // share one production; field_access (prec 10) still grabs `.field` so
    // `p.x` is `field_access(object: name, field)`, and the loader classifies
    // a name as ref / qualified / projection via SymbolKind.
    _atom_term: $ => choice(
      $.string_literal,
      $.integer_literal,
      $.float_literal,
      $.boolean_literal,
      $.variable_term,
      $.fn_term,
      $.application,
      $.set_literal,
      $.collection_literal,
      $.tuple_literal,
      $.nested_implication,
      $.paren_expr,
      $.ref_term,
      $.prefix_term,
      $.field_access,
      prec(-1, $.name),
    ),

    // Nested implication inside a forall binder, used as a body goal.
    // (forall(?h, ?rest), Q(?h), Q(?rest) -: P(cons(head: ?h, tail: ?rest)))
    // Used by the auto-generated induction principles in proposal 025
    // for the inductive-step case of recursive constructors.
    nested_implication: $ => seq(
      '(',
      'forall',
      '(',
      commaSep1(field('binder', $.variable)),
      ')',
      ',',
      field('antecedents', $.rule_body),
      '-:',
      field('consequent', $.rule_body),
      ')',
    ),

    // Field access: ?x.y, expr.field — dot projection.
    // Desugars to field_access(object, field) in the converter.
    // Highest precedence, left-associative: ?x.y.z → (?x.y).z
    field_access: $ => prec.left(10, seq(
      field('object', $._atom_term),
      '.',
      field('field', $.identifier),
    )),

    // Variable with optional inline description(s): ?x {< text >}?
    // If descriptions are present, the variable term must end with '?'.
    variable_term: $ => choice(
      $.variable,
      seq(
        $.variable,
        repeat1(field('description', $.description_block)),
        '?'
      ),
    ),

    // ? = anonymous variable (each occurrence distinct, like _ in Prolog)
    // ?name = named variable (shared within scope)
    // Single token: ?name must be written without whitespace.
    variable: $ => token(seq('?', optional(/[a-zA-Z_][a-zA-Z0-9_-]*/))),

    // The functor excludes the fully-dotted `name` rule so that
    // bare `p.x` in argument position reduces to field_access
    // instead of being eaten as a nested fn_term name. The `(`
    // after field_access is the disambiguator with $._atom_term.
    // For `Name[bindings]` callees, the same trailing-token rule
    // splits: `(` → typed call, `.` → sort companion, neither → bare
    // instantiation term.
    fn_term: $ => seq(
      field('name', choice(
        $.name,
        $.field_access,
        $.variable,
        $.application,
      )),
      '(',
      commaSep($._fn_arg),
      ')',
    ),

    // A lambda may appear directly as a call argument:
    // `map(xs, lambda x -> f(x))`. The lambda body is an `_expr_body`
    // (infix_term / fn_term / etc.), none of which can consume the
    // argument-separating comma, so `commaSep($._fn_arg)` still delimits
    // arguments cleanly even though `lambda_expr` is `prec.right`.
    _fn_arg: $ => choice(
      $._term,
      $.named_arg,
      $.lambda_expr,
    ),

    named_arg: $ => seq(
      field('name', $.identifier),
      ':',
      field('value', $._term),
    ),

    // Set literal: {x, y, z} desugars to add(add(add(empty(), x), y), z).
    // {} desugars to empty().
    // No ambiguity: bare {…} = set literal, Name{…} = application.
    // prec(-2) so block-level { (rule/operation blocks, sort/namespace bodies)
    // takes precedence when ambiguous.
    set_literal: $ => prec(-2, seq('{', commaSep($._term), '}')),

    // Collection literal: [x, y, z] or [x, y | rest].
    // Bare [...] = collection literal, Name[...] = application (disambiguated by leading Name).
    // prec(-2) like set_literal/tuple_literal to avoid conflicts with block-level constructs.
    collection_literal: $ => prec(-2, choice(
      seq('[', ']'),                                                          // empty
      seq('[', commaSep1($._term), optional(seq('|', field('tail', $._term))), ']'),
    )),

    // Tuple literal: (1, 2) or (x: 1, y: 2) or () for unit.
    // Uses _fn_arg to allow both positional and named args;
    // all-or-nothing naming enforced in the converter.
    // prec(-2) to avoid conflict with parenthesized expressions.
    tuple_literal: $ => prec(-2, choice(
      seq('(', ')'),                                                      // unit
      seq('(', $._fn_arg, ',', commaSep1($._fn_arg), optional(','), ')'), // 2+ elements
    )),

    ref_term: $ => seq('Ref', '(', $.name, ')'),

    // Operator token: any sequence of operator chars (maximal munch).
    // prec(-1) ensures keywords and other tokens take priority.
    // Note: `!` is excluded — it is a dedicated prefix token. `!=` is
    // handled as an explicit anonymous token in `_infix_op`.
    operator_symbol: $ => token(prec(-1, /[+\-*/%^|&=<>~]+/)),

    // Flat infix: all operators at one grammar level, Pratt resolver handles precedence.
    infix_term: $ => prec(1, seq(
      $._atom_term,
      repeat1(seq($._infix_op, $._atom_term)),
    )),

    _infix_op: $ => choice(
      $.operator_symbol,                    // symbolic: +, ->, >=, ...
      '!=',                                 // explicit (since ! not in operator_symbol)
      '@',                                  // effect annotation on arrows
      'or', 'and', 'mod', 'div',            // word operators
    ),

    // Parenthesized expression: (a) = a. Grouping only, no tuple.
    // Distinguished from tuple_literal by absence of comma.
    paren_expr: $ => seq('(', $._term, ')'),

    // Prefix operators: restricted to specific tokens that cannot
    // start an _infix_op, avoiding ambiguity in flat chains.
    prefix_term: $ => seq($._prefix_op, $._atom_term),

    _prefix_op: $ => choice('!', 'not'),

    // =========================================================
    // Expressions (operation bodies)
    // =========================================================

    _expr_body: $ => choice(
      $.match_expr,
      $.if_expr,
      $.let_chain,
      $.lambda_expr,
      $._term,
    ),

    match_expr: $ => prec.right(seq(
      'match', field('scrutinee', $._term),
      repeat1($.match_branch),
    )),

    match_branch: $ => seq(
      'case', field('pattern', $._pattern),
      optional(seq('|', field('guard', $._term))),
      '->', field('body', $._expr_body),
    ),

    if_expr: $ => prec.right(seq(
      'if', field('condition', $._term),
      'then', field('then', $._expr_body),
      'else', field('else', $._expr_body),
    )),

    // Block-style let: let x = value \n body (no 'in' keyword).
    // Optional `: type` annotation between pattern and `=` (proposal 035
    // form (1)): supplies an expected-type hint to the typer for the
    // value position. The annotation also fixes the bound variable's
    // type for the body, so subsequent uses can disambiguate against it
    // (e.g. `Map.empty()` -> Map[K = String, V = Int] from the LHS).
    let_chain: $ => prec.right(seq(
      'let', field('pattern', $._pattern),
      optional(seq(':', field('type', $._type))),
      '=', field('value', $._expr_body),
      field('body', $._expr_body),
    )),

    // A lambda binds exactly ONE parameter, which is a full `_pattern`.
    // Multiple parameters are expressed by destructuring a (named) tuple:
    // `lambda (a, b) -> add(a, b)`. This is deliberate, not a limitation —
    // a single pattern binder avoids comma ambiguity when a lambda is passed
    // as a function argument (`map(lambda x -> x + 1, xs)`): the tuple parens
    // delimit the parameter, so the top-level commas unambiguously separate
    // the enclosing call's arguments. See proposal 018 §Lambda.
    lambda_expr: $ => prec.right(seq(
      'lambda', field('param', $._pattern),
      '->', field('body', $._expr_body),
    )),

    // =========================================================
    // Patterns
    // =========================================================

    _pattern: $ => choice(
      $.pattern_constructor,
      $.pattern_tuple,
      $.pattern_literal,
      $.pattern_wildcard,
      $.pattern_var,
    ),

    pattern_wildcard: $ => prec(2, '_'),

    pattern_var: $ => $.identifier,

    pattern_literal: $ => choice(
      $.string_literal,
      $.integer_literal,
      $.float_literal,
      $.boolean_literal,
    ),

    pattern_constructor: $ => seq(
      field('name', $.name),
      '(',
      commaSep($._pattern_arg),
      ')',
    ),

    // Pattern argument: positional or named (name: pattern)
    _pattern_arg: $ => choice(
      $.named_pattern_field,
      $._pattern,
    ),

    named_pattern_field: $ => seq(
      field('field_name', $.identifier),
      ':',
      field('field_pattern', $._pattern),
    ),

    pattern_tuple: $ => choice(
      seq('(', ')'),
      seq('(', $._pattern, ',', commaSep1($._pattern), ')'),
    ),

    // =========================================================
    // Types
    // =========================================================

    _type: $ => choice(
      $.simple_type,
      $.application,
      $.variable_term,
      $.tuple_type,
      $.arrow_type,
    ),

    // Arrow type: (A) -> B  or  (a: A, b: B) -> C  or  () -> A
    //   or  (A) -> B @ E         (single effect)
    //   or  (A) -> B @ {E1, E2}  (effect set, mirrors operation `effects`)
    // Uses arrow_params (named, not hidden) to avoid field-bleeding on parens.
    arrow_type: $ => prec.right(seq(
      field('params', $.arrow_params),
      '->',
      field('return_type', $._type),
      optional(seq('@', field('effect', $._effect_set))),
    )),

    arrow_params: $ => choice(
      seq('(', ')'),                                                // () -> A
      seq('(', $._tuple_type_arg, ')'),                             // (A) -> B  /  (a: A) -> B
      seq('(', $._tuple_type_arg, ',', commaSep1($._tuple_type_arg), ')'),  // (A, B) -> C
    ),

    tuple_type: $ => choice(
      seq('(', ')'),
      seq('(', $._tuple_type_arg, ',', commaSep1($._tuple_type_arg), optional(','), ')'),
    ),

    _tuple_type_arg: $ => choice($._type, $.field_decl),

    simple_type: $ => $.name,

    // WI-311: unified type/term application — `Name[bindings]`. Merges the
    // former parameterized_type (type position) and instantiation_term (term
    // position) into one node; the converter classifies type-vs-term by
    // position, the loader by SymbolKind. The base is the dotted `$.name` so
    // fully-qualified parameterized types parse (`scala.prelude.List[Int]`).
    // prec(1): when a name is followed by `[`, prefer shifting into the
    // application bracket over reducing the name to `simple_type` and treating
    // `[…]` as a trailing `meta_block` (abstract-sort / operation-return have an
    // optional meta_block); `name`'s prec.left otherwise wins that shift-reduce.
    application: $ => prec(1, seq(
      field('name', $.name),
      '[',
      commaSep1($.sort_binding),
      ']',
    )),

    // =========================================================
    // Bindings (for tool params etc.)
    // =========================================================

    bindings: $ => seq(
      '{',
      commaSep1(seq($.identifier, ':', $._term)),
      '}',
    ),

    // =========================================================
    // Names and identifiers
    // =========================================================

    name: $ => prec.left(sep1(reserved('none', $.identifier), '.')),

    identifier: $ => reserved('none', $._identifier_token),

    _identifier_token: $ => /[a-zA-Z_][a-zA-Z0-9_-]*/,

    // =========================================================
    // Literals
    // =========================================================

    string_literal: $ => /"([^"\\]|\\.)*"/,
    integer_literal: $ => /-?[0-9]+/,
    float_literal: $ => /-?[0-9]+\.[0-9]+/,
    boolean_literal: $ => choice('true', 'false'),
    duration_literal: $ => /[0-9]+(?:ms|s|m|h|d)/,

    // =========================================================
    // Comments
    // =========================================================

    line_comment: $ => /--[^\n]*/,

    block_comment: $ => seq(
      '{-',
      /[^-]*(-+[^}\-][^-]*)*/,
      '-}',
    ),
  },
});

// =========================================================
// Helper functions
// =========================================================

function commaSep(rule) {
  return optional(commaSep1(rule));
}

function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)));
}

function sep1(rule, separator) {
  return seq(rule, repeat(seq(separator, rule)));
}
