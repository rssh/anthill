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
      optional($.visibility),
      'sort',
      field('name', $.name),
      '=',
      field('definition', $._type),
      repeat(field('description', $.description_block)),
      optional($.meta_block),
    ),

    sort_with_body: $ => seq(
      optional($.visibility),
      'sort',
      field('name', $.name),
      repeat(field('description', $.description_block)),
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
      optional($.visibility),
      'operation',
      field('name', $.name),
      '(',
      optional(commaSep1($.param)),
      ')',
      '->',
      field('return_type', $._type),
      repeat($.operation_clause),
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
      optional($.visibility),
      'entity',
      field('name', $.name),
      optional(seq('(', commaSep1($.field_decl), ')')),
      optional($.meta_block),
    ),

    fact_declaration: $ => seq(
      'fact',
      field('term', $._term),
      optional($.meta_block),
    ),

    constraint_declaration: $ => seq(
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

    describe_declaration: $ => seq(
      'describe',
      field('target', $.name),
      repeat1(field('content', $.description_block)),
    ),

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
      $.string_literal,
      $.integer_literal,
      $.float_literal,
      $.boolean_literal,
      $.variable_term,
      $.fn_term,
      $.instantiation_term,
      $.ref_term,
      $.infix_term,
      $.identifier,
    ),

    // Variable with optional inline description(s): ?x {< text >} {< more >}
    // prec.right ensures the description_block is greedily consumed by
    // variable_term rather than by an enclosing rule (e.g., abstract_sort).
    variable_term: $ => prec.right(seq(
      $.variable,
      repeat(field('description', $.description_block)),
    )),

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

    // Instantiation term: Eq{Int}, List{T = Int}, etc.
    // Same syntax as parameterized_type but in term position.
    // Used for: fact Eq{Int}, fact Numeric{Int}, etc.
    instantiation_term: $ => seq(
      field('name', $.name),
      '{',
      commaSep1($.sort_binding),
      '}',
    ),

    ref_term: $ => seq('Ref', '(', $.name, ')'),

    // Infix sugar: a > b, a + b, a = b, etc.
    infix_term: $ => choice(
      prec.left(1, seq($._term, '=', $._term)),
      prec.left(2, seq($._term, choice('>', '>=', '<', '<='), $._term)),
      prec.left(3, seq($._term, choice('+', '-'), $._term)),
      prec.left(4, seq($._term, '*', $._term)),
    ),

    // =========================================================
    // Types
    // =========================================================

    _type: $ => choice(
      $.simple_type,
      $.parameterized_type,
      $.variable_term,
    ),

    simple_type: $ => $.name,

    parameterized_type: $ => seq(
      $.name,
      '{',
      commaSep1($.sort_binding),
      '}',
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
