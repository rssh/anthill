theory Anthill_Kernel
  imports Complex_Main
begin

section \<open>Anthill Kernel Language --- Formal Specification\<close>

text \<open>
  This theory formalises the core constructs of the Anthill kernel language:
  terms, sorts, rules (Horn clauses with denials), operations, namespaces,
  first-order substitution and unification, trust levels, and basic
  knowledge-base operations.

  Reference: docs/kernel-language.md in the Anthill repository.
\<close>

subsection \<open>Symbols and Identifiers\<close>

type_synonym symbol = string
type_synonym var_id = nat

subsection \<open>Literals\<close>

datatype literal =
    LitInt int
  | LitFloat rat  \<comment> \<open>rational approximation of IEEE 754\<close>
  | LitString string
  | LitBool bool

subsection \<open>Terms\<close>

text \<open>
  An @{text aterm} (anthill term) is the universal representation in the
  kernel language.  Sorts are themselves terms (types-are-terms principle).
  The prefix avoids a clash with the Isabelle built-in @{text term} type.
\<close>

datatype fn_arg =
    Positional aterm
  | Named symbol aterm
and aterm =
    Const literal
  | Var var_id
  | Fn symbol "fn_arg list"
  | Ref symbol
  | Quoted string string
  | Bottom

subsection \<open>Sorts\<close>

datatype sort_kind = Abstract | Defined | Constructor

text \<open>Sort identifiers are just terms (types-are-terms).\<close>
type_synonym sort_id = aterm

subsection \<open>Reflect Types\<close>

text \<open>
  These types mirror the entities defined in @{verbatim \<open>stdlib/anthill/reflect/reflect.anthill\<close>}.
  They specify the structured fact shapes emitted by the loader and queried
  by the reflection API.
\<close>

text \<open>Cons-list encoding: terms are stored as @{text "cons(head: x, tail: ...)"} / @{text "nil()"}.\<close>

fun list_to_cons :: "aterm list \<Rightarrow> aterm" where
  "list_to_cons [] = Fn ''nil'' []"
| "list_to_cons (x # xs) = Fn ''cons'' [Named ''head'' x, Named ''tail'' (list_to_cons xs)]"

text \<open>
  @{text LiteralRepr}: structural decomposition of constants without circularity.
  Replaces the old @{text "ConstRepr(type_name, value)"} which stringified everything.
\<close>

datatype literal_repr =
    IntLiteral int
  | FloatLiteral rat
  | StringLiteral string
  | BoolLiteral bool

text \<open>
  @{text TermRepr}: structural decomposition of a term for introspection.
  @{text name} fields in @{text FnRepr} and @{text RefRepr} are Symbol references
  (stored as @{text "Ref sym"} terms), not plain strings.
\<close>

datatype term_repr =
    ConstRepr literal_repr
  | VarRepr string              \<comment> \<open>variable name\<close>
  | FnRepr aterm "term_repr list"  \<comment> \<open>name is a Symbol (Ref term), args are children\<close>
  | RefRepr aterm               \<comment> \<open>name is a Symbol (Ref term)\<close>
  | QuotedRepr string string    \<comment> \<open>language, source\<close>

text \<open>
  @{text SortInfo}: structured fact emitted for each sort-with-body declaration.
  All name fields are Symbol references; list fields use cons/nil encoding.
\<close>

record sort_info =
  si_name         :: aterm       \<comment> \<open>Ref to sort symbol\<close>
  si_definition   :: aterm       \<comment> \<open>Var for abstract, sort term for defined\<close>
  si_constructors :: "aterm list"
  si_operations   :: "aterm list"
  si_parameters   :: "aterm list"
  si_requires     :: "aterm list"

text \<open>Build a @{text SortInfo} fact term with named arguments.\<close>

definition sort_info_term :: "sort_info \<Rightarrow> aterm" where
  "sort_info_term si \<equiv>
     Fn ''SortInfo'' [
       Named ''name'' (si_name si),
       Named ''definition'' (si_definition si),
       Named ''constructors'' (list_to_cons (si_constructors si)),
       Named ''operations'' (list_to_cons (si_operations si)),
       Named ''parameters'' (list_to_cons (si_parameters si)),
       Named ''requires'' (list_to_cons (si_requires si))
     ]"

text \<open>
  @{text FieldInfo}: parameter description within an @{text OperationInfo}.
\<close>

definition field_info_term :: "symbol \<Rightarrow> aterm \<Rightarrow> aterm" where
  "field_info_term name type_term \<equiv>
     Fn ''FieldInfo'' [
       Named ''name'' (Const (LitString name)),
       Named ''type_name'' type_term
     ]"

text \<open>
  @{text OperationInfo}: structured fact emitted for each operation declaration.
  @{text sort_context} is @{text "some(value: Ref(sort))"} or @{text "none()"}.
\<close>

definition op_info_term ::
  "aterm \<Rightarrow> aterm \<Rightarrow> aterm list \<Rightarrow> aterm \<Rightarrow> aterm list \<Rightarrow> aterm" where
  "op_info_term name_ref sort_ctx param_terms return_term effect_terms \<equiv>
     Fn ''OperationInfo'' [
       Named ''name'' name_ref,
       Named ''sort_context'' sort_ctx,
       Named ''params'' (list_to_cons param_terms),
       Named ''return_type'' return_term,
       Named ''effects'' (list_to_cons effect_terms)
     ]"

text \<open>Helpers for Option encoding.\<close>

definition option_some :: "aterm \<Rightarrow> aterm" where
  "option_some v \<equiv> Fn ''some'' [Named ''value'' v]"

definition option_none :: aterm where
  "option_none \<equiv> Fn ''none'' []"

subsection \<open>Trust Levels\<close>

text \<open>
  Trust is attached to facts, not agents.  The ordering captures
  verification strength; @{text axiom} and @{text decision} sit outside
  the main chain.
\<close>

datatype trust =
    Proved
  | Verified
  | Tested nat
  | Empirical
  | Proposed
  | Stale
  | Axiom
  | Decision

text \<open>Rank function: lower number = higher trust.\<close>

fun trust_rank :: "trust \<Rightarrow> nat" where
  "trust_rank Proved      = 0"
| "trust_rank Verified    = 1"
| "trust_rank (Tested _)  = 2"
| "trust_rank Empirical   = 3"
| "trust_rank Proposed    = 4"
| "trust_rank Stale       = 5"
| "trust_rank Axiom       = 0"
| "trust_rank Decision    = 0"

text \<open>Ordering on the main verification chain (excludes axiom/decision).\<close>

fun on_verification_chain :: "trust \<Rightarrow> bool" where
  "on_verification_chain Axiom    = False"
| "on_verification_chain Decision = False"
| "on_verification_chain _        = True"

definition trust_le :: "trust \<Rightarrow> trust \<Rightarrow> bool" (infix "\<le>\<^sub>t" 50) where
  "t1 \<le>\<^sub>t t2 \<equiv>
     on_verification_chain t1 \<and> on_verification_chain t2 \<and>
     (trust_rank t1 < trust_rank t2 \<or>
      (trust_rank t1 = trust_rank t2 \<and>
       (case (t1, t2) of
          (Tested n1, Tested n2) \<Rightarrow> n1 \<ge> n2
        | _ \<Rightarrow> True)))"

text \<open>Basic sanity: proved is at least as trusted as every chain member.\<close>

lemma proved_top: "on_verification_chain t \<Longrightarrow> Proved \<le>\<^sub>t t"
  by (cases t) (simp_all add: trust_le_def)

lemma tested_monotone: "n1 \<ge> n2 \<Longrightarrow> Tested n1 \<le>\<^sub>t Tested n2"
  by (simp add: trust_le_def)

subsection \<open>Rules (Horn Clauses)\<close>

text \<open>
  A rule has an optional name, a head term, and a list of body terms.
  \<^item> Derivation rule: non-Bottom head, non-empty body.
  \<^item> Ground assertion (fact): non-Bottom head, empty body.
  \<^item> Denial (integrity constraint): head = Bottom.
\<close>

record arule =
  arule_name :: "symbol option"
  arule_head :: aterm
  arule_body :: "aterm list"

definition is_fact :: "arule \<Rightarrow> bool" where
  "is_fact r \<equiv> arule_body r = [] \<and> arule_head r \<noteq> Bottom"

definition is_denial :: "arule \<Rightarrow> bool" where
  "is_denial r \<equiv> arule_head r = Bottom"

definition is_derivation :: "arule \<Rightarrow> bool" where
  "is_derivation r \<equiv> arule_body r \<noteq> [] \<and> arule_head r \<noteq> Bottom"

lemma rule_trichotomy:
  "arule_head r = Bottom \<or>
   (arule_head r \<noteq> Bottom \<and> arule_body r = []) \<or>
   (arule_head r \<noteq> Bottom \<and> arule_body r \<noteq> [])"
  by auto

subsection \<open>Effects\<close>

text \<open>
  Effects give operations a state-passing interpretation.  An operation
  \<^verbatim>\<open>op(x1: A1, ..., xm: Am) -> R effects (Modifies S, Reads T, ...)\<close>
  is interpreted in the non-monadic style as
  \<^verbatim>\<open>op_e : Env \<times> A1 \<times> ... \<times> Am \<rightarrow> (R \<times> Env \<times> Event list) + Error\<close>
  where @{text Env} maps resource names to their current state.

  Effects are represented as open (kind, target) pairs.  The well-known
  kinds Modifies, Reads, Emits, Errors, Requires are defined in stdlib;
  additional effect kinds may be introduced by libraries.
\<close>

record effect =
  eff_kind   :: symbol
  eff_target :: symbol

text \<open>
  Well-known effect kinds.  These abbreviations mirror the five standard
  effect constructors defined in the Anthill standard library.
\<close>

abbreviation eff_Modifies :: "symbol \<Rightarrow> effect" where
  "eff_Modifies s \<equiv> \<lparr> eff_kind = ''Modifies'', eff_target = s \<rparr>"

abbreviation eff_Reads :: "symbol \<Rightarrow> effect" where
  "eff_Reads s \<equiv> \<lparr> eff_kind = ''Reads'', eff_target = s \<rparr>"

abbreviation eff_Emits :: "symbol \<Rightarrow> effect" where
  "eff_Emits s \<equiv> \<lparr> eff_kind = ''Emits'', eff_target = s \<rparr>"

abbreviation eff_Errors :: "symbol \<Rightarrow> effect" where
  "eff_Errors s \<equiv> \<lparr> eff_kind = ''Errors'', eff_target = s \<rparr>"

abbreviation eff_Requires :: "symbol \<Rightarrow> effect" where
  "eff_Requires s \<equiv> \<lparr> eff_kind = ''Requires'', eff_target = s \<rparr>"

subsubsection \<open>Effect environment\<close>

text \<open>
  The environment maps resource names to their current state (as terms).
  An effectful operation takes an environment and arguments, and either
  succeeds with a result, an updated environment, and emitted events,
  or fails with an error term.
\<close>

type_synonym env = "symbol \<rightharpoonup> aterm"

record effectful_result =
  er_value  :: aterm
  er_env    :: env
  er_events :: "aterm list"

type_synonym effectful_op = "env \<Rightarrow> aterm list \<Rightarrow> (effectful_result + aterm)"
  \<comment> \<open>Inl = success, Inr = error term\<close>

subsubsection \<open>Resource projections\<close>

definition reads_resources :: "effect list \<Rightarrow> symbol set" where
  "reads_resources effs \<equiv>
     {s. \<exists>e \<in> set effs. eff_kind e = ''Reads'' \<and> eff_target e = s}
   \<union> {s. \<exists>e \<in> set effs. eff_kind e = ''Modifies'' \<and> eff_target e = s}"

definition modifies_resources :: "effect list \<Rightarrow> symbol set" where
  "modifies_resources effs \<equiv>
     {s. \<exists>e \<in> set effs. eff_kind e = ''Modifies'' \<and> eff_target e = s}"

definition emits_events :: "effect list \<Rightarrow> symbol set" where
  "emits_events effs \<equiv>
     {s. \<exists>e \<in> set effs. eff_kind e = ''Emits'' \<and> eff_target e = s}"

definition required_capabilities :: "effect list \<Rightarrow> symbol set" where
  "required_capabilities effs \<equiv>
     {s. \<exists>e \<in> set effs. eff_kind e = ''Requires'' \<and> eff_target e = s}"

definition error_types :: "effect list \<Rightarrow> symbol set" where
  "error_types effs \<equiv>
     {s. \<exists>e \<in> set effs. eff_kind e = ''Errors'' \<and> eff_target e = s}"

text \<open>Reads is always a superset of Modifies (you read what you mutate).\<close>

lemma modifies_subset_reads:
  "modifies_resources effs \<subseteq> reads_resources effs"
  by (auto simp: reads_resources_def modifies_resources_def)

subsubsection \<open>Effect-env condition\<close>

text \<open>
  An effectful operation respects its effect-env condition if it only modifies the
  resources declared in its @{text Modifies} effects.
\<close>

definition respects_effect_env :: "effect list \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "respects_effect_env effs e_before e_after \<equiv>
     \<forall>s. s \<notin> modifies_resources effs \<longrightarrow> e_after s = e_before s"

text \<open>A pure (effect-free) operation preserves the entire environment.\<close>

lemma pure_effect_env: "respects_effect_env [] e e"
  by (simp add: respects_effect_env_def modifies_resources_def)

text \<open>
  Effect-env weakening: declaring more effects makes the constraint easier
  to satisfy.
\<close>

lemma effect_env_weaken:
  "\<lbrakk> set effs1 \<subseteq> set effs2; respects_effect_env effs1 e1 e2 \<rbrakk>
   \<Longrightarrow> respects_effect_env effs2 e1 e2"
  by (auto simp: respects_effect_env_def modifies_resources_def)

subsubsection \<open>Well-behavedness\<close>

subsection \<open>Operations\<close>

record operation =
  op_name    :: symbol
  op_params  :: "(symbol \<times> sort_id) list"
  op_return  :: sort_id
  op_requires :: "aterm list"
  op_ensures  :: "aterm list"
  op_effects  :: "effect list"

text \<open>
  An effectful implementation is well-behaved w.r.t.\ its declared
  effects when every successful execution respects the effect-env condition and all
  required capabilities are present in the environment.
\<close>

definition capabilities_present :: "effect list \<Rightarrow> env \<Rightarrow> bool" where
  "capabilities_present effs e \<equiv>
     \<forall>c \<in> required_capabilities effs. e c \<noteq> None"

definition well_behaved :: "operation \<Rightarrow> effectful_op \<Rightarrow> bool" where
  "well_behaved spec impl \<equiv>
     \<forall>e args res.
       capabilities_present (op_effects spec) e \<longrightarrow>
       impl e args = Inl res \<longrightarrow>
       respects_effect_env (op_effects spec) e (er_env res)"

text \<open>
  Composition of two effectful operations threads the environment
  and concatenates emitted events.
\<close>

definition compose_effectful ::
  "effectful_op \<Rightarrow> effectful_op \<Rightarrow> effectful_op" where
  "compose_effectful f g \<equiv> \<lambda>e args.
     (case f e args of
        Inr err \<Rightarrow> Inr err
      | Inl r1 \<Rightarrow>
          (case g (er_env r1) [er_value r1] of
             Inr err \<Rightarrow> Inr err
           | Inl r2 \<Rightarrow>
               Inl \<lparr> er_value = er_value r2,
                     er_env = er_env r2,
                     er_events = er_events r1 @ er_events r2 \<rparr>))"

text \<open>
  Effect-env composition: if @{text f} respects @{text effs1} and @{text g}
  respects @{text effs2}, their composition respects @{text "effs1 @ effs2"}.
\<close>

lemma compose_effect_env:
  assumes wf: "respects_effect_env effs1 e0 e1"
      and wg: "respects_effect_env effs2 e1 e2"
  shows "respects_effect_env (effs1 @ effs2) e0 e2"
  using assms
  by (auto simp: respects_effect_env_def modifies_resources_def)

text \<open>A pure operation (no effects) is trivially well-behaved.\<close>

lemma pure_well_behaved:
  assumes pure: "\<And>e args. \<exists>v. impl e args = Inl \<lparr> er_value = v, er_env = e, er_events = [] \<rparr>"
  shows "well_behaved (spec\<lparr> op_effects := [] \<rparr>) impl"
  unfolding well_behaved_def
proof (intro allI impI)
  fix e args res
  assume "impl e args = Inl res"
  moreover obtain v where "impl e args = Inl \<lparr> er_value = v, er_env = e, er_events = [] \<rparr>"
    using pure by blast
  ultimately have "er_env res = e" by force
  thus "respects_effect_env (op_effects (spec\<lparr> op_effects := [] \<rparr>)) e (er_env res)"
    by (simp add: pure_effect_env)
qed

subsubsection \<open>Description Facts\<close>

text \<open>
  Description blocks produce facts of the form @{text "Description(target, text)"}.
  The syntax @{verbatim \<open>describe Name {< text >}\<close>} is sugar for asserting a
  fact with sort @{text Description} and domain equal to the enclosing scope.
  Descriptions replace the former @{text Unspecified} term variant --- they live
  in the knowledge base as ordinary facts rather than as a special term node.
\<close>

subsubsection \<open>Monadic interpretation\<close>

text \<open>
  The monadic interpretation views an effectful operation as a
  computation in a combined monad @{text "M\<^sub>E"} that layers:
  \<^item> @{text "StateT Env"} for @{text Reads}/@{text Modifies},
  \<^item> @{text "WriterT (Event list)"} for @{text Emits},
  \<^item> @{text "ExceptT Error"} for @{text Errors},
  \<^item> @{text "ReaderT Caps"} for @{text Requires}.

  An operation @{text "op(x1: A1, \<dots>, xm: Am) -> R  effects E"} is
  interpreted as @{text "op\<^sub>m : A1 \<rightarrow> \<dots> \<rightarrow> Am \<rightarrow> M\<^sub>E(R)"}.

  We define the monad concretely as a state-error-writer triple and
  provide @{text return\<^sub>m} and @{text bind\<^sub>m}.
\<close>

type_synonym 'a eff_monad = "env \<Rightarrow> (('a \<times> env \<times> aterm list) + aterm)"

definition return_eff :: "'a \<Rightarrow> 'a eff_monad" where
  "return_eff x \<equiv> \<lambda>e. Inl (x, e, [])"

definition bind_eff :: "'a eff_monad \<Rightarrow> ('a \<Rightarrow> 'b eff_monad) \<Rightarrow> 'b eff_monad" where
  "bind_eff m f \<equiv> \<lambda>e.
     (case m e of
        Inr err \<Rightarrow> Inr err
      | Inl (a, e', evts1) \<Rightarrow>
          (case f a e' of
             Inr err \<Rightarrow> Inr err
           | Inl (b, e'', evts2) \<Rightarrow> Inl (b, e'', evts1 @ evts2)))"

definition get_resource :: "symbol \<Rightarrow> aterm option eff_monad" where
  "get_resource s \<equiv> \<lambda>e. Inl (e s, e, [])"

definition put_resource :: "symbol \<Rightarrow> aterm \<Rightarrow> unit eff_monad" where
  "put_resource s v \<equiv> \<lambda>e. Inl ((), e(s \<mapsto> v), [])"

definition emit_event :: "aterm \<Rightarrow> unit eff_monad" where
  "emit_event evt \<equiv> \<lambda>e. Inl ((), e, [evt])"

definition throw_error :: "aterm \<Rightarrow> 'a eff_monad" where
  "throw_error err \<equiv> \<lambda>_. Inr err"

definition require_capability :: "symbol \<Rightarrow> unit eff_monad" where
  "require_capability c \<equiv> \<lambda>e.
     (case e c of
        Some _ \<Rightarrow> Inl ((), e, [])
      | None   \<Rightarrow> Inr (Fn ''missing_capability'' [Positional (Ref c)]))"

text \<open>Monad laws.\<close>

lemma return_bind [simp]: "bind_eff (return_eff x) f = f x"
  by (auto simp add: bind_eff_def return_eff_def fun_eq_iff
           split: sum.splits prod.splits)

lemma bind_return [simp]: "bind_eff m return_eff = m"
  by (auto simp add: bind_eff_def return_eff_def fun_eq_iff split: sum.splits prod.splits)

lemma bind_assoc:
  "bind_eff (bind_eff m f) g = bind_eff m (\<lambda>x. bind_eff (f x) g)"
  by (simp add: bind_eff_def fun_eq_iff split: sum.splits prod.splits)

subsubsection \<open>Equivalence of interpretations\<close>

text \<open>
  Convert between the state-passing (@{typ effectful_op}) and monadic
  (@{typ "aterm eff_monad"}) representations.
\<close>

definition to_monad :: "effectful_op \<Rightarrow> aterm list \<Rightarrow> aterm eff_monad" where
  "to_monad f args \<equiv> \<lambda>e.
     (case f e args of
        Inr err \<Rightarrow> Inr err
      | Inl r  \<Rightarrow> Inl (er_value r, er_env r, er_events r))"

definition from_monad :: "(aterm list \<Rightarrow> aterm eff_monad) \<Rightarrow> effectful_op" where
  "from_monad m \<equiv> \<lambda>e args.
     (case m args e of
        Inr err \<Rightarrow> Inr err
      | Inl (v, e', evts) \<Rightarrow> Inl \<lparr> er_value = v, er_env = e', er_events = evts \<rparr>)"

text \<open>Round-trip: monadic \<open>\<rightarrow>\<close> state-passing \<open>\<rightarrow>\<close> monadic is identity.\<close>

lemma monad_roundtrip:
  "to_monad (from_monad m) args = m args"
  by (simp add: to_monad_def from_monad_def fun_eq_iff
                split: sum.splits prod.splits)

text \<open>Round-trip: state-passing \<open>\<rightarrow>\<close> monadic \<open>\<rightarrow>\<close> state-passing is identity.\<close>

lemma state_roundtrip:
  "from_monad (\<lambda>args. to_monad f args) = f"
proof (intro ext)
  fix e args
  show "from_monad (\<lambda>args. to_monad f args) e args = f e args"
    by (cases "f e args")
       (auto simp: to_monad_def from_monad_def split: sum.splits)
qed

text \<open>
  The frame condition is preserved by the correspondence: a monadic
  computation respects the effect-env condition iff the corresponding state-passing
  operation does.
\<close>

lemma effect_env_to_monad:
  assumes "from_monad m e args = Inl res"
  and "respects_effect_env effs e (er_env res)"
  shows "\<exists>v e' evts. m args e = Inl (v, e', evts)
         \<and> (\<forall>s. s \<notin> modifies_resources effs \<longrightarrow> e' s = e s)"
  using assms
  by (auto simp: from_monad_def respects_effect_env_def
           split: sum.splits prod.splits)

subsection \<open>Visibility and Namespaces\<close>

datatype visibility = Internal | Export | Public

datatype module_item =
    MI_Sort sort_id sort_kind
  | MI_Entity aterm
  | MI_Rule arule
  | MI_Operation operation
  | MI_Requires aterm  \<comment> \<open>standalone requires: type expression as term\<close>
  | MI_SubModule module_body
and module_body = \<comment> \<open>mb_primary_sort: Some s = sort-with-body; None = namespace\<close>
  ModuleBody
    (mb_name : symbol)
    (mb_primary_sort : "sort_id option")
    (mb_items : "module_item list")
    (mb_visibility : visibility)

fun direct_entities :: "module_item list \<Rightarrow> aterm list" where
  "direct_entities [] = []"
| "direct_entities (MI_Entity e # rest) = e # direct_entities rest"
| "direct_entities (MI_Sort _ _ # rest) = direct_entities rest"
| "direct_entities (MI_Rule _ # rest) = direct_entities rest"
| "direct_entities (MI_Operation _ # rest) = direct_entities rest"
| "direct_entities (MI_Requires _ # rest) = direct_entities rest"
| "direct_entities (MI_SubModule _ # rest) = direct_entities rest"

definition determine_sort_kind :: "module_item list \<Rightarrow> sort_kind" where
  "determine_sort_kind items \<equiv>
     (if direct_entities items \<noteq> [] then Defined else Abstract)"

subsection \<open>Substitution\<close>

type_synonym subst = "var_id \<rightharpoonup> aterm"

text \<open>
  Chase a term through the substitution, following variable-to-variable
  bindings.  Termination requires an acyclic substitution; we use
  @{text partial_function} to sidestep the proof obligation.
\<close>

definition acyclic_subst :: "subst \<Rightarrow> bool" where
  "acyclic_subst \<sigma> \<equiv> wf {(v', v). \<sigma> v = Some (Var v')}"

partial_function (tailrec) chase :: "subst \<Rightarrow> aterm \<Rightarrow> aterm" where
  "chase \<sigma> t =
     (case t of
        Var v \<Rightarrow> (case \<sigma> v of
                    None   \<Rightarrow> Var v
                  | Some t' \<Rightarrow> chase \<sigma> t')
      | _ \<Rightarrow> t)"

text \<open>
  Apply a substitution to a term.  Variables are looked up once via
  @{text chase} (which follows variable chains) and the result is
  substituted without further recursive lookup.  This matches the Rust
  implementation where @{text materialize} walks the term applying
  pre-chased bindings.
\<close>

fun apply_subst_arg :: "subst \<Rightarrow> fn_arg \<Rightarrow> fn_arg"
and apply_subst :: "subst \<Rightarrow> aterm \<Rightarrow> aterm" where
  "apply_subst \<sigma> (Const l) = Const l"
| "apply_subst \<sigma> (Var v) = chase \<sigma> (Var v)"
| "apply_subst \<sigma> (Fn f args) = Fn f (map (apply_subst_arg \<sigma>) args)"
| "apply_subst \<sigma> (Ref s) = Ref s"
| "apply_subst \<sigma> (Quoted lang src) = Quoted lang src"
| "apply_subst \<sigma> Bottom = Bottom"
| "apply_subst_arg \<sigma> (Positional t) = Positional (apply_subst \<sigma> t)"
| "apply_subst_arg \<sigma> (Named n t) = Named n (apply_subst \<sigma> t)"

subsection \<open>Free Variables\<close>

fun fv_arg :: "fn_arg \<Rightarrow> var_id set"
and fv :: "aterm \<Rightarrow> var_id set" where
  "fv (Const _) = {}"
| "fv (Var v) = {v}"
| "fv (Fn _ args) = \<Union>(set (map fv_arg args))"
| "fv (Ref _) = {}"
| "fv (Quoted _ _) = {}"
| "fv Bottom = {}"
| "fv_arg (Positional t) = fv t"
| "fv_arg (Named _ t) = fv t"

definition ground :: "aterm \<Rightarrow> bool" where
  "ground t \<equiv> fv t = {}"

subsection \<open>Occurs Check\<close>

text \<open>
  Syntactic occurs check: does variable @{term v} occur anywhere in
  term @{term t}?  This is used after chasing, so no substitution
  parameter is needed.
\<close>

fun occurs_in_arg :: "var_id \<Rightarrow> fn_arg \<Rightarrow> bool"
and occurs_in :: "var_id \<Rightarrow> aterm \<Rightarrow> bool" where
  "occurs_in v (Const _) = False"
| "occurs_in v (Var w) = (v = w)"
| "occurs_in v (Fn _ args) = (\<exists>a \<in> set args. occurs_in_arg v a)"
| "occurs_in v (Ref _) = False"
| "occurs_in v (Quoted _ _) = False"
| "occurs_in v Bottom = False"
| "occurs_in_arg v (Positional t) = occurs_in v t"
| "occurs_in_arg v (Named _ t) = occurs_in v t"

lemma occurs_in_arg_iff_fv: "occurs_in_arg v1 a1 \<longleftrightarrow> v1 \<in> fv_arg a1"
  and occurs_in_iff_fv: "occurs_in v0 t0 \<longleftrightarrow> v0 \<in> fv t0"
  by (induction v1 a1 and v0 t0 rule: occurs_in_arg_occurs_in.induct) auto

subsection \<open>Unification\<close>

text \<open>
  First-order unification with occurs check.  We define the algorithm
  on positional argument lists (the common case).  Named arguments are
  matched by name in a wrapper.
\<close>

datatype unify_error =
    Clash
  | OccursCheck
  | ArityMismatch

fun unify_args :: "subst \<Rightarrow> fn_arg list \<Rightarrow> fn_arg list \<Rightarrow> (subst + unify_error)"
and unify :: "subst \<Rightarrow> aterm \<Rightarrow> aterm \<Rightarrow> (subst + unify_error)" where
  "unify \<sigma> (Var v) t2 =
     (let t2' = chase \<sigma> t2 in
      (case t2' of
         Var w \<Rightarrow> (if v = w then Inl \<sigma> else Inl (\<sigma>(v \<mapsto> t2')))
       | _ \<Rightarrow> (if occurs_in v t2'
              then Inr OccursCheck
              else Inl (\<sigma>(v \<mapsto> t2')))))"
| "unify \<sigma> t1 (Var v) =
     (let t1' = chase \<sigma> t1 in
      (case t1' of
         Var w \<Rightarrow> (if v = w then Inl \<sigma> else Inl (\<sigma>(v \<mapsto> t1')))
       | _ \<Rightarrow> (if occurs_in v t1'
              then Inr OccursCheck
              else Inl (\<sigma>(v \<mapsto> t1')))))"
| "unify \<sigma> (Const l1) (Const l2) =
     (if l1 = l2 then Inl \<sigma> else Inr Clash)"
| "unify \<sigma> (Fn f1 args1) (Fn f2 args2) =
     (if f1 = f2 \<and> length args1 = length args2
      then unify_args \<sigma> args1 args2
      else Inr Clash)"
| "unify \<sigma> (Ref s1) (Ref s2) =
     (if s1 = s2 then Inl \<sigma> else Inr Clash)"
| "unify \<sigma> Bottom Bottom = Inl \<sigma>"
| "unify \<sigma> _ _ = Inr Clash"
| "unify_args \<sigma> [] [] = Inl \<sigma>"
| "unify_args \<sigma> (Positional t1 # rest1) (Positional t2 # rest2) =
     (case unify \<sigma> t1 t2 of
        Inl \<sigma>' \<Rightarrow> unify_args \<sigma>' rest1 rest2
      | Inr e \<Rightarrow> Inr e)"
| "unify_args \<sigma> (Named n1 t1 # rest1) (Named n2 t2 # rest2) =
     (if n1 = n2
      then (case unify \<sigma> t1 t2 of
              Inl \<sigma>' \<Rightarrow> unify_args \<sigma>' rest1 rest2
            | Inr e \<Rightarrow> Inr e)
      else Inr Clash)"
| "unify_args \<sigma> _ _ = Inr ArityMismatch"

text \<open>Reflexivity: unifying a term with itself always succeeds.\<close>

lemma unify_refl_const: "unify \<sigma> (Const l) (Const l) = Inl \<sigma>"
  by simp

lemma unify_refl_ref: "unify \<sigma> (Ref s) (Ref s) = Inl \<sigma>"
  by simp

lemma unify_refl_bottom: "unify \<sigma> Bottom Bottom = Inl \<sigma>"
  by simp

subsection \<open>Knowledge Base\<close>

type_synonym fact_id = nat

record fact_entry =
  fe_term     :: aterm
  fe_sort     :: sort_id
  fe_domain   :: sort_id
  fe_meta     :: "aterm option"
  fe_retracted :: bool

record knowledge_base =
  kb_facts   :: "fact_entry list"
  kb_subsort :: "(sort_id \<times> sort_id) list"  \<comment> \<open>(child, parent) pairs\<close>
  kb_sorts   :: "(sort_id \<times> sort_kind) list"
  kb_next_var :: nat

definition empty_kb :: knowledge_base where
  "empty_kb \<equiv> \<lparr>
     kb_facts = [],
     kb_subsort = [],
     kb_sorts = [],
     kb_next_var = 0
   \<rparr>"

subsubsection \<open>Subsort relation\<close>

text \<open>
  The subsort relation is the reflexive-transitive closure of the
  declared subsort pairs.
\<close>

definition subsort_rel :: "knowledge_base \<Rightarrow> (sort_id \<times> sort_id) set" where
  "subsort_rel kb \<equiv> set (kb_subsort kb)"

definition is_subtype :: "knowledge_base \<Rightarrow> sort_id \<Rightarrow> sort_id \<Rightarrow> bool" where
  "is_subtype kb s1 s2 \<equiv> (s1, s2) \<in> (subsort_rel kb)\<^sup>*"

lemma is_subtype_refl: "is_subtype kb s s"
  by (simp add: is_subtype_def)

lemma is_subtype_trans:
  "\<lbrakk> is_subtype kb a b; is_subtype kb b c \<rbrakk> \<Longrightarrow> is_subtype kb a c"
  by (simp add: is_subtype_def rtrancl_trans)

subsubsection \<open>Fact operations\<close>

text \<open>
  Find an existing active fact with the same term, sort, and domain.
  Used to make @{text assert_fact} idempotent --- asserting the same
  fact twice returns the existing fact id without duplicating it.
\<close>

fun find_fact_aux ::
  "fact_entry list \<Rightarrow> nat \<Rightarrow> aterm \<Rightarrow> sort_id \<Rightarrow> sort_id
   \<Rightarrow> fact_id option" where
  "find_fact_aux [] _ _ _ _ = None"
| "find_fact_aux (e # es) idx t s d =
     (if fe_term e = t \<and> fe_sort e = s \<and> fe_domain e = d
         \<and> \<not> fe_retracted e
      then Some idx
      else find_fact_aux es (Suc idx) t s d)"

definition find_existing_fact ::
  "knowledge_base \<Rightarrow> aterm \<Rightarrow> sort_id \<Rightarrow> sort_id
   \<Rightarrow> fact_id option" where
  "find_existing_fact kb t s d \<equiv>
     find_fact_aux (kb_facts kb) 0 t s d"

lemma find_fact_aux_valid:
  "find_fact_aux es idx t s d = Some fid \<Longrightarrow>
   fid < idx + length es"
proof (induction es arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons e es)
  show ?case
  proof (cases "fe_term e = t \<and> fe_sort e = s \<and> fe_domain e = d \<and> \<not> fe_retracted e")
    case True then show ?thesis using Cons.prems by simp
  next
    case False
    then have "find_fact_aux es (Suc idx) t s d = Some fid"
      using Cons.prems by auto
    then have "fid < Suc idx + length es" using Cons.IH by blast
    then show ?thesis by simp
  qed
qed

lemma find_existing_fact_valid:
  "find_existing_fact kb t s d = Some fid \<Longrightarrow>
   fid < length (kb_facts kb)"
  unfolding find_existing_fact_def
  using find_fact_aux_valid by fastforce

definition assert_fact ::
  "knowledge_base \<Rightarrow> aterm \<Rightarrow> sort_id \<Rightarrow> sort_id \<Rightarrow> aterm option
   \<Rightarrow> knowledge_base \<times> fact_id" where
  "assert_fact kb t s d m \<equiv>
     (case find_existing_fact kb t s d of
        Some fid \<Rightarrow> (kb, fid)
      | None \<Rightarrow>
          let fid = length (kb_facts kb);
              entry = \<lparr> fe_term = t, fe_sort = s, fe_domain = d,
                         fe_meta = m, fe_retracted = False \<rparr>;
              kb' = kb\<lparr> kb_facts := kb_facts kb @ [entry] \<rparr>
          in (kb', fid))"

definition retract :: "knowledge_base \<Rightarrow> fact_id \<Rightarrow> knowledge_base" where
  "retract kb fid \<equiv>
     kb\<lparr> kb_facts := list_update (kb_facts kb) fid
           ((kb_facts kb ! fid)\<lparr> fe_retracted := True \<rparr>) \<rparr>"

definition active_facts :: "knowledge_base \<Rightarrow> (fact_id \<times> fact_entry) list" where
  "active_facts kb \<equiv>
     filter (\<lambda>(_, e). \<not> fe_retracted e)
            (zip [0..<length (kb_facts kb)] (kb_facts kb))"

subsubsection \<open>Query by pattern matching (one-way unification)\<close>

definition match_fact ::
  "aterm \<Rightarrow> fact_entry \<Rightarrow> (subst + unify_error)" where
  "match_fact pattern entry \<equiv> unify Map.empty pattern (fe_term entry)"

definition query ::
  "knowledge_base \<Rightarrow> aterm \<Rightarrow> (fact_id \<times> subst) list" where
  "query kb pattern \<equiv>
     [(fid, \<sigma>). (fid, entry) \<leftarrow> active_facts kb,
                \<sigma> \<leftarrow> (case match_fact pattern entry of
                        Inl \<sigma> \<Rightarrow> [\<sigma>] | Inr _ \<Rightarrow> [])]"

subsubsection \<open>Sort registration\<close>

definition register_sort ::
  "knowledge_base \<Rightarrow> sort_id \<Rightarrow> sort_kind \<Rightarrow> knowledge_base" where
  "register_sort kb s k \<equiv>
     kb\<lparr> kb_sorts := kb_sorts kb @ [(s, k)] \<rparr>"

definition register_subsort ::
  "knowledge_base \<Rightarrow> sort_id \<Rightarrow> sort_id \<Rightarrow> knowledge_base" where
  "register_subsort kb child parent \<equiv>
     kb\<lparr> kb_subsort := kb_subsort kb @ [(child, parent)] \<rparr>"

fun register_constructor_subsorts ::
  "knowledge_base \<Rightarrow> sort_id \<Rightarrow> aterm list \<Rightarrow> knowledge_base" where
  "register_constructor_subsorts kb _ [] = kb"
| "register_constructor_subsorts kb parent (ctor # rest) =
     register_constructor_subsorts
       (register_subsort (register_sort kb ctor Constructor) ctor parent)
       parent rest"

subsubsection \<open>Module loading\<close>

fun load_module_item :: "knowledge_base \<Rightarrow> sort_id \<Rightarrow> module_item \<Rightarrow> knowledge_base"
and load_module_items :: "knowledge_base \<Rightarrow> sort_id \<Rightarrow> module_item list \<Rightarrow> knowledge_base"
and load_module_body :: "knowledge_base \<Rightarrow> module_body \<Rightarrow> knowledge_base"
where
  "load_module_item kb sc (MI_Sort s k) = register_sort kb s k"
| "load_module_item kb sc (MI_Entity e) =
     fst (assert_fact kb e (Fn ''Entity'' []) sc None)"
| "load_module_item kb sc (MI_Rule r) =
     fst (assert_fact kb (arule_head r) (Fn ''Rule'' []) sc None)"
| "load_module_item kb sc (MI_Operation oper) =
     (let name_ref = Ref (op_name oper);
          sort_ctx = (case sc of
                        Fn s [] \<Rightarrow> option_some (Ref s)
                      | _ \<Rightarrow> option_none);
          param_terms = map (\<lambda>(n, t). field_info_term n t) (op_params oper);
          effect_terms = map (\<lambda>e. Fn (eff_kind e) [Positional (Ref (eff_target e))]) (op_effects oper);
          oi = op_info_term name_ref sort_ctx param_terms (op_return oper) effect_terms
      in fst (assert_fact kb oi (Fn ''Operation'' []) sc None))"
| "load_module_item kb sc (MI_Requires t) =
     fst (assert_fact kb (Fn ''Requires'' [Positional t]) (Fn ''Requirement'' []) sc None)"
| "load_module_item kb sc (MI_SubModule mb) =
     load_module_body kb mb"
| "load_module_items kb sc [] = kb"
| "load_module_items kb sc (i # rest) =
     load_module_items (load_module_item kb sc i) sc rest"
| "load_module_body kb (ModuleBody name ps items vis) =
     (let scope = Fn name [];
          kb1 = (case ps of
                   None \<Rightarrow> fst (assert_fact kb scope (Fn ''Namespace'' []) scope None)
                 | Some s \<Rightarrow> register_constructor_subsorts
                               (register_sort kb s (determine_sort_kind items))
                               s (direct_entities items));
          kb2 = load_module_items kb1 scope items;
          \<comment> \<open>Emit SortInfo fact for sort-with-body declarations\<close>
          kb3 = (case ps of
                   None \<Rightarrow> kb2
                 | Some s \<Rightarrow>
                     let has_entities = direct_entities items \<noteq> [];
                         def_term = (if has_entities then s else Var (kb_next_var kb2));
                         ctor_refs = map (\<lambda>e. case e of Fn f _ \<Rightarrow> Ref f | _ \<Rightarrow> e)
                                        (direct_entities items);
                         si = \<lparr> si_name = Ref name,
                                si_definition = def_term,
                                si_constructors = ctor_refs,
                                si_operations = [],
                                si_parameters = [],
                                si_requires = [] \<rparr>
                     in fst (assert_fact kb2 (sort_info_term si) (Fn ''Sort'' []) scope None))
      in kb3)"

subsubsection \<open>Fresh variables\<close>

definition fresh_var :: "knowledge_base \<Rightarrow> knowledge_base \<times> var_id" where
  "fresh_var kb \<equiv> (kb\<lparr> kb_next_var := kb_next_var kb + 1 \<rparr>, kb_next_var kb)"

subsection \<open>Denial Checking\<close>

text \<open>
  Note: denial checking and forward chaining are specified here as a
  reference for the formal semantics.  They are not yet implemented in the
  Stage 0 Rust layer, which currently performs only fact assertion and
  pattern-matching queries.
\<close>

text \<open>
  A denial @{text "\<bottom> :- B1, \<dots>, Bn"} is violated when all body atoms
  are provable.  We check this after each fact assertion.
\<close>

definition body_satisfied ::
  "knowledge_base \<Rightarrow> aterm list \<Rightarrow> bool" where
  "body_satisfied kb body \<equiv>
     (\<exists>\<sigma>. \<forall>atom \<in> set body. query kb (apply_subst \<sigma> atom) \<noteq> [])"

definition denial_violated ::
  "knowledge_base \<Rightarrow> arule \<Rightarrow> bool" where
  "denial_violated kb r \<equiv> is_denial r \<and> body_satisfied kb (arule_body r)"

definition kb_consistent ::
  "knowledge_base \<Rightarrow> arule list \<Rightarrow> bool" where
  "kb_consistent kb denials \<equiv> \<not>(\<exists>d \<in> set denials. denial_violated kb d)"

subsection \<open>Forward Chaining (Single Step)\<close>

text \<open>
  Given a set of derivation rules, one forward-chaining step derives
  all new facts whose bodies are satisfied.
\<close>

definition derivable_facts ::
  "knowledge_base \<Rightarrow> arule list \<Rightarrow> aterm set" where
  "derivable_facts kb rules \<equiv>
     {apply_subst \<sigma> (arule_head r) |r \<sigma>.
        r \<in> set rules \<and> is_derivation r \<and>
        (\<forall>atom \<in> set (arule_body r).
           query kb (apply_subst \<sigma> atom) \<noteq> [])}"

subsection \<open>Builtins\<close>

text \<open>
  Builtins are operations dispatched directly by the resolver, not via
  KB fact matching.  Each builtin is identified by its qualified name and
  has a specific execution semantics.
\<close>

datatype builtin_tag =
    BT_NonVar         \<comment> \<open>@{text "anthill.reflect.nonvar(?x)"}: succeeds if ?x is non-variable\<close>
  | BT_Ground         \<comment> \<open>@{text "anthill.reflect.ground(?x)"}: succeeds if ?x is fully ground\<close>
  | BT_QualifiedName  \<comment> \<open>@{text "qualified_name(?sym, ?result)"}: Symbol \<rightarrow> full name string\<close>
  | BT_ShortName      \<comment> \<open>@{text "short_name(?sym, ?result)"}: Symbol \<rightarrow> last segment string\<close>
  | BT_LookupSymbol   \<comment> \<open>@{text "lookup_symbol(?name, ?result)"}: String \<rightarrow> Symbol (fails if not found)\<close>

datatype builtin_result =
    BR_Success
  | BR_SuccessWithBindings subst
  | BR_Delay
  | BR_Failure

text \<open>
  All builtins delay when their first positional argument is an unbound variable.
  @{text NonVar} and @{text Ground} produce no bindings (test-only).
  @{text QualifiedName}, @{text ShortName}, and @{text LookupSymbol} bind the
  second positional argument to the computed result.
\<close>

subsection \<open>Properties\<close>

text \<open>Asserting a fact preserves or extends the fact store.\<close>

lemma assert_fact_preserves_or_extends:
  "assert_fact kb t s d m = (kb', fid) \<Longrightarrow>
   length (kb_facts kb') = length (kb_facts kb) \<or>
   length (kb_facts kb') = length (kb_facts kb) + 1"
  by (auto simp: assert_fact_def Let_def split: option.splits)

text \<open>Asserting a new fact (no existing duplicate) increases the fact count.\<close>

lemma assert_new_fact_increases:
  "\<lbrakk> assert_fact kb t s d m = (kb', fid);
     find_existing_fact kb t s d = None \<rbrakk> \<Longrightarrow>
   length (kb_facts kb') = length (kb_facts kb) + 1"
  by (auto simp: assert_fact_def Let_def)

text \<open>Asserting an existing fact is idempotent.\<close>

lemma assert_fact_idempotent:
  "find_existing_fact kb t s d = Some fid \<Longrightarrow>
   assert_fact kb t s d m = (kb, fid)"
  by (simp add: assert_fact_def)

text \<open>The returned fact id is valid.\<close>

lemma assert_fact_id_valid:
  "assert_fact kb t s d m = (kb', fid) \<Longrightarrow>
   fid < length (kb_facts kb')"
  by (auto simp: assert_fact_def Let_def
           dest: find_existing_fact_valid split: option.splits)

text \<open>Subsort reflexivity and transitivity hold by construction.\<close>

lemma subtype_refl_trans:
  "is_subtype kb a a"
  "is_subtype kb a b \<Longrightarrow> is_subtype kb b c \<Longrightarrow> is_subtype kb a c"
  by (simp_all add: is_subtype_def rtrancl_trans)

text \<open>
  Empty KB is consistent with any set of denials whose bodies are
  non-empty (a denial with empty body is an unconditional contradiction).
\<close>

lemma query_empty_kb: "query empty_kb p = []"
  by (simp add: query_def active_facts_def empty_kb_def)

lemma empty_kb_consistent:
  assumes "\<forall>d \<in> set denials. arule_body d \<noteq> []"
  shows "kb_consistent empty_kb denials"
  using assms
  by (auto simp add: kb_consistent_def denial_violated_def
                     body_satisfied_def query_empty_kb)

text \<open>Nested entities are not constructors of the outer scope.\<close>

lemma nested_entity_not_constructor:
  "direct_entities [MI_SubModule m] = []"
  by simp

text \<open>Constructor subsort registration: every direct entity becomes a subtype of the parent.\<close>

lemma register_constructor_subsorts_mono:
  "set (kb_subsort kb) \<subseteq> set (kb_subsort (register_constructor_subsorts kb parent es))"
proof (induction es arbitrary: kb)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  have "set (kb_subsort kb)
        \<subseteq> set (kb_subsort (register_subsort (register_sort kb a Constructor) a parent))"
    by (auto simp: register_subsort_def register_sort_def)
  also have "\<dots> \<subseteq> set (kb_subsort (register_constructor_subsorts
                        (register_subsort (register_sort kb a Constructor) a parent)
                        parent es))"
    using Cons.IH by blast
  finally show ?case by simp
qed

lemma register_constructor_subsorts_adds_pair:
  assumes "e \<in> set es"
  shows "(e, parent) \<in> set (kb_subsort (register_constructor_subsorts kb parent es))"
  using assms
proof (induction es arbitrary: kb)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  show ?case
  proof (cases "a = e")
    case True
    have "(e, parent) \<in> set (kb_subsort
            (register_subsort (register_sort kb e Constructor) e parent))"
      by (auto simp: register_subsort_def register_sort_def)
    then show ?thesis
      using True register_constructor_subsorts_mono[of
        "register_subsort (register_sort kb e Constructor) e parent" parent es]
      by (auto simp: subset_iff)
  next
    case False
    then have "e \<in> set es" using Cons.prems by simp
    then show ?thesis using Cons.IH by simp
  qed
qed

lemma constructor_subsort_registration:
  assumes "e \<in> set (direct_entities items)"
  and "kb' = register_constructor_subsorts kb s (direct_entities items)"
  shows "is_subtype kb' e s"
  using assms register_constructor_subsorts_adds_pair
  by (auto simp: is_subtype_def subsort_rel_def intro: r_into_rtrancl)

text \<open>Name uniqueness predicate for well-formed scopes.\<close>

definition well_formed_scope :: "module_item list \<Rightarrow> bool" where
  "well_formed_scope items \<equiv>
     \<forall>m1 m2. MI_SubModule m1 \<in> set items \<and> MI_SubModule m2 \<in> set items
       \<and> mb_name m1 = mb_name m2 \<longrightarrow> m1 = m2"

end
