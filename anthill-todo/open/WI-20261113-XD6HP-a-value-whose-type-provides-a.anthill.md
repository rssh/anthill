## Attributes

- id: WI-20261113-XD6HP-a-value-whose-type-provides-a
- created: 2026-11-13T14:49:34Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T14:49:34Z

- acceptance: cargo-test

- tags: proposal-073

## Description

A VALUE WHOSE TYPE PROVIDES A SPEC OVER A PARAMETER, PASSED WHERE THE SPEC IS EXPECTED, IS AN INSTANCE: THE VALUE, WITH ITS TYPE'S TABLE CARRIED ALONGSIDE (proposal 073 §2; decided with the user 2026-11-13, replacing part 2's reading of WI-20261105-P0QGF). x: Additive is a value of a type that provides Additive, and x.T is that type: a call at x.T in the body takes its dictionary from x, and x itself is a value of x.T (x + y runs). A call passes the value at x; the compiler builds the table at load from the argument's type, by kernel-language §8.7's order, or forwards the caller's own under requires Additive[T = X], and pairs the two, as a value of an abstract type is paired since P0QGF part 1 (Instance(dict, value), instance-values.md). Every argument is written: there is no implicit instance parameter. A spec application, Additive[T = Int64], is a type wherever it is written, and is refused at x: a type where a value is expected. WITNESS (the user's, WI-817's): operation applyBoth(f: (x: Additive, y: x.T) -> x.T) -> (Int64, Float) = let ints = f(1, 2)  let floats = f(3.0, 4.3)  (ints, floats), applied to lambda (x: Additive, y: x.T) -> x + y, answers (3, 7.3): one closure, each call handing it its own value and table, nothing required of applyBoth or of the lambda. TODAY (cb7da1eb) f(1, 2) is refused ('type Int64 has no member T', the arrow's x.T read at the argument 1; the operation spelling 'expected Additive, got Int64'). DECIDED 2026-11-13: with g: (x: Additive, a: x.T, b: x.T) -> x.T, g(1, 2) is refused (arity) and g(1, 2, 3) runs (x = 1 with Int64's table, a = 2, b = 3); add2(Additive[T = Int64], 2, 3) — 5 since part 2 — is refused, Additive[T = Int64] only ever meaning the type. WHAT PART 2 DELIVERED THAT CHANGES (rows in wi_p0qgf_spec_instance_values_test, wi_p0qgf_lambda_instance_test, wi_dndzf_arrow_parameter_projects_another_test): add2(2, 2, 3) runs to 5 (was kept refused); a body x + a runs (was kept refused); ints(), sum2's add2(Additive[T = X], a, b), zeroOf(Additive[T = Int64]), sumWith's f(Additive[T = X], a, b) and every lambda row pass a value instead (sum2 as add2(a, a, b), zeroOf(5) answering 0); InstanceConversion::SpecApplication and the application read as the instance go; asType() -> Type = Additive[T = Int64] still answers the type. STAYS: x.zero() refused (a dot passes x, zero takes none); y: x.T holds y to x's type, so f(1, 2.5) is refused; an if over 1 and 2.5 at x fixes no type and is refused (no value chooses a type, 058 §3.9). TO RE-MEASURE under the new reading: the 2026-11-13 member rule (Car.size(y: Sp) behind Sp.size(y: T) at Sp[T = Self] refused, signature.rs Narrower::Receiver by_spec_over_parameter), now that a Car may be passed at y: Sp. SPEC: kernel-language §8.2 — the sentence 'a position typed at the spec takes no value of a provider's sort, and a value typed at the spec is refused where the parameter is expected' and the 2026-11-13 paragraph 'A value typed at a spec over a parameter is an instance …' (with probeAt / viaB / viaP) — rewritten; the text agreed with the user BEFORE implementing. ACCEPTANCE: applyBoth (3, 7.3); g(1, 2, 3) 6 and g(1, 2) refused; add2(2, 2, 3) 5; x + a in a body; sum2(2, 3) 5 and sum2(1.5, 2.5) 4.0 through the clause; zeroOf(5) 0; two instances of two types in one call; a rule body's call; a host call; refused: add2(Additive[T = Int64], 2, 3), f(1, 2.5), a value of a type no provision answers (add2(true, true, false)); asType() the type. Back-outs measured per part; full workspace green via rustland/scripts/test.sh; families green on both carriers.

## Changes

### 2026-11-13T14:51:23Z — feedback — claude

THE PRINCIPLE BEHIND THE CHANGE (the user, 2026-11-13): a written form has one reading; part 2's second reading of a spec application — Additive[T = Int64] as the type where a Type is expected and as the table where Additive is expected — is incorrect, and goes. A second reading is admitted only in rare cases, each argued on its own. So: x: Additive is a parameter whose value has type Additive, a parameter that holds a type is written t: Type, and Additive[T = Int64] is a type wherever it is written.

