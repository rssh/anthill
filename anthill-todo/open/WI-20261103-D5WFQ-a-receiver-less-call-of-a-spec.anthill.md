## Attributes

- id: WI-20261103-D5WFQ-a-receiver-less-call-of-a-spec
- created: 2026-11-03T05:11:46Z

- status: Open
- status_agent: claude
- status_at: 2026-11-03T05:11:46Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RECEIVER-LESS CALL OF A SPEC'S DEFAULT BODY LOADS CLEAN WHERE ITS FRAME CANNOT BE BUILT, AND FAILS AT RUN TIME: a bracket that leaves a parameter out where the provisions answering the rest say it apart, and a woven call of a default with a `requires` of its own whose spec has a second provider. Both left by WI-20261102-ME8WR (its review's skipped findings; the NOT COVERED note of wi_me8wr_receiver_less_default_test).

MEASURED on 372ec4fa, each as a program run by `anthill run`.

1. The provisions say the left-out parameter apart:

  sort Pc2
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation both() -> C = emp()
  end
  sort Bag
    entity bint
    entity bstr
  end
  sort WInt
    provides Pc2[C = Bag, Element = Int64]
    operation emp() -> Bag = bint()
  end
  sort WStr
    provides Pc2[C = Bag, Element = String]
    operation emp() -> Bag = bstr()
  end

- `Pc2[C = Bag].both()` in an operation body loads clean and dies "operation has no body: Pc2.emp"; in a rule (`rule rBoth(?n) :- ?n <=> Pc2[C = Bag].both()`, `rBoth(bstr())`) it raises relation_floundered(unify(bstr, both)).
- `Pc2[C = Bag, Element = String].both()` answers `bstr`.
- `open_slots_said` answers Apart here; `bind_params_the_provisions_say` then binds nothing, and the step-3 refusal of a bracket naming no instance is gated on a complete goal (kb/typing/apply.rs), so nothing refuses. With one such provision the completion fixes `Element` and the call answers (ME8WR).

2. The default's own requirement, through the clause's dictionary, its spec provided twice:

  sort Unit
    sort T = ?
    operation unit() -> T
  end
  sort Bit
    entity t
    entity f
    provides Unit[T = Bit]
    operation unit() -> Bit = t()
  end
  sort Num
    entity num(n: Int64)
    provides Unit[T = Num]
    operation unit() -> Num = num(n: 0)
  end
  sort Pc2
    sort C = ?
    sort Element = ?
    operation fill(xs: List[T = Element]) -> C
    operation both() -> C requires Unit[T = Element] = fill([Unit.unit[T = Element]()])
  end
  sort Bag
    entity bnil
    entity bsome(b: Bit)
    provides Pc2[C = Bag, Element = Bit]
    operation fill(xs: List[T = Bit]) -> Bag = match xs
      case nil() -> bnil()
      case cons(x, rest) -> bsome(b: x)
  end
  sort Sat[C]
    requires Pc2[C = C, Element = Bit]
    rule model(vs: C) :- vs <=> Pc2.both()
  end

- `Sat[C = Bag].model(bsome(b: t()))` panics: "bridged_value: internal evaluator error bridging `Pc2.both`: … DeferToRequirement: requirement param `__req_unit` not bound in caller frame (… frame binds ["__req_self"])" (kb/resolve.rs).
- Without `Num` the same call answers 1.
- The woven route stamps nothing for the callee's own `requires`, and the bridge's dictionary entry derives it from the argument values (`fill_missing_op_scoped_slots`, eval/mod.rs); `both()` takes none, so the derivation is left with two providers of `Unit`. The dictionary says `Element = Bit`, which `Unit[T = Element]` reads, and `Bit` is the one provider of `Unit[T = Bit]`.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site):
- 1 is refused where the bracket is written, naming the parameter the provisions say apart, in an operation body, in a rule and in a const.
- 2 answers 1 for `bsome(b: t())`, 0 for `bsome(b: f())` and 1 for the open model, with `Num` declared; also at a second provider of `Pc2` (`Rev`), and with the default's requirement at a parameter the dictionary binds to a provider other than the first in load order.
- CONTROLS: wi_me8wr_receiver_less_default_test unchanged, in particular `a_woven_default_derives_its_own_requirement` (one provider of `Unit`) and the full bracket `Pc2[C = Bag, Element = String].both()` above.

