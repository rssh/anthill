/// Tree-sitter grammar for the Anthill kernel language + Stage 0 sugar.
///
/// The kernel has 4 constructs: namespace, sort, rule, operation.
/// Sugar adds: entity, fact, constraint, operation/rule blocks.
/// Stage 0 adds: project, tool, workitem, feedback blocks.
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
    // rule <head> could start a single rule or a rule block
    [$.rule_declaration, $.rule_entry],
    // operation <name>(...) could start a single operation or an operation block
    [$.operation_declaration, $.operation_entry],
    // (removed: abstract_sort vs sort_with_body conflict — `= ?` disambiguates)
    // After operation clauses, `requires` could be another clause or a standalone declaration
    [$.operation_declaration],
    [$.variable_term],
    // name [ could be parameterized_type or simple_type followed by something else
    [$.simple_type, $.parameterized_type],
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
      $._stage0_declaration,
    ),

    // =========================================================
    // Kernel declarations
    // =========================================================

    _declaration: $ => choice(
      $.namespace_declaration,
      $.abstract_sort,
      $.sort_with_body,
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
    ),

    // =========================================================
    // Stage 0 sugar declarations
    // =========================================================

    _stage0_declaration: $ => choice(
      $.project_declaration,
      $.tool_declaration,
      $.workitem_declaration,
      $.feedback_declaration,
      $.import_tools_declaration,
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

    sort_binding: $ => choice(
      seq(
        field('param', $.name),
        optional(seq('=', field('type', $._type))),
      ),
      // Variable as standalone binding: Read{?}, Effect{?r}
      field('type', $.variable_term),
    ),

    export_clause: $ => seq(
      'export',
      commaSep1($.name),
    ),

    _body_namespace: $ => choice(
      seq('{', repeat($._namespace_content), '}'),
      seq(repeat($._namespace_content), 'end', optional($.name)),
    ),

    _namespace_content: $ => choice(
      $.namespace_declaration,
      $.abstract_sort,
      $.sort_with_body,
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
      $.export_clause,
    ),

    _body_sort: $ => choice(
      seq('{', repeat($._sort_content), '}'),
      seq(repeat($._sort_content), 'end', optional($.name)),
    ),

    _sort_content: $ => choice(
      $.namespace_declaration,
      $.abstract_sort,
      $.sort_with_body,
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
      $.export_clause,
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
      $._body_sort,
      optional($.meta_block),
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

    rule_declaration: $ => seq(
      repeat(field('description', $.description_block)),
      'rule',
      optional(seq(field('label', $.name), ':')),
      field('head', $.rule_head),
      optional(seq(':-', field('body', $.rule_body))),
      optional($.meta_block),
    ),

    rule_head: $ => choice(
      '⊥',
      $._term,
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
      '(',
      optional(commaSep1($.param)),
      ')',
      '->',
      field('return_type', $._type),
      repeat($.operation_clause),
      optional(seq('=', field('body', $._expr_body))),
      optional($.meta_block),
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
    ),

    requires_declaration: $ => seq(
      'requires',
      field('type', $._type),
    ),

    requires_clause: $ => seq('requires', $.rule_body),
    ensures_clause: $ => seq('ensures', $.rule_body),
    effects_clause: $ => seq('effects', '(', commaSep1($._type), ')'),

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
      field('head', $.rule_body),
      optional(seq(':-', field('guard', $.rule_body))),
      optional($.meta_block),
    ),

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
    // Sugar: operation block, rule block
    // =========================================================

    operation_block: $ => seq(
      'operation',
      choice(
        seq('{', repeat($.operation_entry), '}'),
        seq(repeat($.operation_entry), 'end'),
      ),
    ),

    operation_entry: $ => seq(
      optional($.visibility),
      field('name', $.name),
      '(',
      optional(commaSep1($.param)),
      ')',
      '->',
      field('return_type', $._type),
      repeat($.operation_clause),
      optional(seq('=', field('body', $._expr_body))),
      optional($.meta_block),
    ),

    rule_block: $ => seq(
      'rule',
      choice(
        seq('{', repeat($.rule_entry), '}'),
        seq(repeat($.rule_entry), 'end'),
      ),
    ),

    rule_entry: $ => seq(
      optional(seq(field('label', $.name), ':')),
      field('head', $.rule_head),
      optional(seq(':-', field('body', $.rule_body))),
      optional($.meta_block),
    ),

    // =========================================================
    // Stage 0: project
    // =========================================================

    project_declaration: $ => seq(
      'project',
      field('name', $.name),
      choice(
        seq('{', $.project_fields, '}'),
        seq($.project_fields, 'end'),
      ),
    ),

    project_fields: $ => seq(
      choice(
        $._project_structure,
        seq('tools', ':', commaSep1($.name)),
        $.import_tools_declaration,
      ),
      repeat($.import_tools_declaration),
      optional(seq('tools', ':', commaSep1($.name))),
      optional(seq('domains', ':', commaSep1($.name))),
      optional($.meta_block),
    ),

    _project_structure: $ => choice(
      $.simple_project_fields,
      $.module_list,
    ),

    simple_project_fields: $ => seq(
      'language', ':', $.identifier,
      optional(seq('build', ':', $.identifier)),
      optional(seq('sources', ':', commaSep1($.source_root))),
    ),

    module_list: $ => seq(
      'modules', ':',
      repeat1($.module_declaration),
    ),

    module_declaration: $ => seq(
      'module',
      field('name', $.name),
      choice(
        seq('{', $.module_fields, '}'),
        seq($.module_fields, 'end'),
      ),
    ),

    module_fields: $ => seq(
      'root', ':', $.string_literal,
      'language', ':', $.identifier,
      optional(seq('build', ':', $.identifier)),
      optional(seq('sources', ':', commaSep1($.source_root))),
      optional($.meta_block),
    ),

    source_root: $ => seq(
      '{',
      'path', ':', $.string_literal, ',',
      optional(seq('language', ':', $.identifier, ',')),
      'scope', ':', $.source_scope,
      '}',
    ),

    source_scope: $ => choice('Main', 'Test', 'Generated', 'Docs'),

    import_tools_declaration: $ => seq(
      'import', 'tools', ':', commaSep1($.name),
    ),

    // =========================================================
    // Stage 0: tool
    // =========================================================

    tool_declaration: $ => seq(
      'tool',
      field('name', $.name),
      choice(
        seq('{', $.tool_fields, '}'),
        seq($.tool_fields, 'end'),
      ),
    ),

    tool_fields: $ => seq(
      'command', ':', $.string_literal,
      optional(seq('args', ':', '[', commaSep1($.string_literal), ']')),
      optional(seq('working_dir', ':', $.string_literal)),
      optional(seq('timeout', ':', $.duration_literal)),
      'success', ':', $.success_criterion,
      optional($.meta_block),
    ),

    success_criterion: $ => choice(
      'ExitZero',
      seq('ExitCode', '(', $.integer_literal, ')'),
      seq('OutputMatches', '(', $.string_literal, ')'),
      seq('Custom', '(', $._term, ')'),
    ),

    // =========================================================
    // Stage 0: workitem
    // =========================================================

    workitem_declaration: $ => seq(
      'workitem',
      field('id', $.name),
      choice(
        seq('{', $.workitem_fields, '}'),
        seq($.workitem_fields, 'end'),
      ),
    ),

    workitem_fields: $ => seq(
      optional(seq('description', ':', $._term)),
      optional(seq('context', ':', repeat1($.context_ref))),
      seq('acceptance', ':', repeat1($.acceptance_criterion)),
      optional(seq('depends_on', ':', '[', commaSep($.name), ']')),
      optional(seq('generates', ':', '[', commaSep1($._term), ']')),
      optional(seq('requires_capability', ':', commaSep1($.capability))),
      seq('status', ':', $.work_status),
      optional($.meta_block),
    ),

    context_ref: $ => choice(
      seq('FileRef', '(', $.string_literal,
        optional(seq(',', 'lines', ':', $.integer_literal, '..', $.integer_literal)),
        ')'),
      seq('FactRef', '(', $.name, ',', $._term, ')'),
      seq('WorkItemRef', '(', $.name, ')'),
    ),

    acceptance_criterion: $ => choice(
      seq('ToolPasses', '(', $.name, optional(seq(',', $.bindings)), ')'),
      seq('FactHolds', '(', $.name, ',', $._term, ')'),
      seq('Compiles', '(', choice($.source_root, seq('module', ':', $.name)), ')'),
      seq('Constraint', '(', $._term, ')'),
    ),

    work_status: $ => choice(
      'Draft',
      'Open',
      seq('Claimed', '(', 'agent', ':', $.string_literal, ',', 'since', ':', $.string_literal, ')'),
      seq('Delivered', '(', 'agent', ':', $.string_literal, ',', 'at', ':', $.string_literal, ')'),
      seq('Verified', '(', 'at', ':', $.string_literal, ')'),
      seq('Rejected', '(', 'reason', ':', $.string_literal, ',', 'at', ':', $.string_literal, ')'),
      seq('ProposalRejected', '(', 'reason', ':', $.string_literal, ',', 'at', ':', $.string_literal, ')'),
      seq('Stale', '(', 'reason', ':', $.string_literal, ',', 'since', ':', $.string_literal, ')'),
    ),

    capability: $ => choice(
      seq('Code', '(', 'languages', ':', '[', commaSep1($.string_literal), ']', ')'),
      'Test',
      'Refine',
      'Review',
      'Decompose',
      'Architect',
      'HumanJudgment',
    ),

    // =========================================================
    // Stage 0: feedback
    // =========================================================

    feedback_declaration: $ => seq(
      'feedback',
      choice(
        seq('{', $.feedback_fields, '}'),
        seq($.feedback_fields, 'end'),
      ),
    ),

    feedback_fields: $ => seq(
      'workitem', ':', $.name,
      'author', ':', $.string_literal,
      'content', ':', $._term,
      'at', ':', $.string_literal,
      optional($.meta_block),
    ),

    // =========================================================
    // Metadata
    // =========================================================

    meta_block: $ => seq(
      '[',
      commaSep1($.meta_entry),
      ']',
    ),

    // Open-keyed: any Name : Term pair. Well-known keys (trust, agent,
    // timestamp, iteration, source, supersedes) have kernel semantics;
    // additional keys are project-defined.
    meta_entry: $ => seq(
      field('key', $.name),
      ':',
      field('value', $._term),
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

    visibility: $ => choice('internal', 'export', 'public'),

    // =========================================================
    // Terms
    // =========================================================

    _term: $ => choice(
      $._atom_term,
      $.infix_term,
    ),

    // Atomic terms: everything except infix_term. Used as operands in
    // infix_term and prefix_term to force flat chains.
    _atom_term: $ => choice(
      $.string_literal,
      $.integer_literal,
      $.float_literal,
      $.boolean_literal,
      $.variable_term,
      $.fn_term,
      $.instantiation_term,
      $.set_literal,
      $.collection_literal,
      $.tuple_literal,
      $.paren_expr,
      $.ref_term,
      $.prefix_term,
      $.field_access,
      prec(-1, $.identifier),
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

    fn_term: $ => seq(
      field('name', $.name),
      '(',
      commaSep($._fn_arg),
      ')',
    ),

    _fn_arg: $ => choice(
      $._term,
      $.named_arg,
    ),

    named_arg: $ => seq(
      field('name', $.identifier),
      ':',
      field('value', $._term),
    ),

    // Instantiation term: Eq[Int], List[T = Int], etc.
    // Same syntax as parameterized_type but in term position.
    // Used for: fact Eq[Int], fact Numeric[Int], etc.
    instantiation_term: $ => seq(
      field('name', $.name),
      '[',
      commaSep1($.sort_binding),
      ']',
    ),

    // Set literal: {x, y, z} desugars to add(add(add(empty(), x), y), z).
    // {} desugars to empty().
    // No ambiguity: bare {…} = set literal, Name{…} = instantiation_term.
    // prec(-2) so block-level { (rule/operation blocks, sort/namespace bodies)
    // takes precedence when ambiguous.
    set_literal: $ => prec(-2, seq('{', commaSep($._term), '}')),

    // Collection literal: [x, y, z] or [x, y | rest].
    // Bare [...] = collection literal, Name[...] = instantiation_term (disambiguated by leading Name).
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
      $.let_expr,
      $.lambda_expr,
      $._term,
    ),

    match_expr: $ => seq(
      'match', field('scrutinee', $._term),
      repeat1($.match_branch),
      'end',
    ),

    match_branch: $ => seq(
      'case', field('pattern', $._pattern),
      '->', field('body', $._expr_body),
    ),

    if_expr: $ => prec.right(seq(
      'if', field('condition', $._term),
      'then', field('then', $._expr_body),
      'else', field('else', $._expr_body),
    )),

    let_expr: $ => prec.right(seq(
      'let', field('pattern', $._pattern),
      '=', field('value', $._expr_body),
      'in', field('body', $._expr_body),
    )),

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
      commaSep($._pattern),
      ')',
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
      $.parameterized_type,
      $.variable_term,
      $.tuple_type,
      $.arrow_type,
    ),

    // Arrow type: (A) -> B  or  (a: A, b: B) -> C  or  () -> A  or  (A) -> B @ E
    // Uses arrow_params (named, not hidden) to avoid field-bleeding on parens.
    arrow_type: $ => prec.right(seq(
      field('params', $.arrow_params),
      '->',
      field('return_type', $._type),
      optional(seq('@', field('effect', $._type))),
    )),

    arrow_params: $ => choice(
      seq('(', ')'),                                                // () -> A
      seq('(', $._type, ')'),                                       // (A) -> B
      seq('(', $._tuple_type_arg, ',', commaSep1($._tuple_type_arg), ')'),  // (A, B) -> C
    ),

    tuple_type: $ => choice(
      seq('(', ')'),
      seq('(', $._tuple_type_arg, ',', commaSep1($._tuple_type_arg), optional(','), ')'),
    ),

    _tuple_type_arg: $ => choice($._type, $.field_decl),

    simple_type: $ => $.name,

    parameterized_type: $ => seq(
      $.name,
      '[',
      commaSep1($.sort_binding),
      ']',
    ),

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

    string_literal: $ => /"[^"]*"/,
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
