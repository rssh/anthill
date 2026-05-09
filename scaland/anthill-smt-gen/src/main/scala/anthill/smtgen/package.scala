package anthill

/** SMT-LIB 2.6 emitter. Mirrors `rustland/anthill-smt-gen/`.
  *
  * v0 scope: discharge a single linear-arithmetic obligation by
  * declaring user-asserted fact fields as Real constants, translating
  * one named rule body to SMT-LIB, asserting the negation of an upper
  * bound on the rule's head, and proving unsat via Z3. Reference
  * spec: `docs/smtlib-forward-mapping.md`.
  *
  * Out of scope for v0: proof cache (WI-214), quantifiers, induction,
  * full reachability, lift_rule_to_implication_clause.
  */
package object smtgen
