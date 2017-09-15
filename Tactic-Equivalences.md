# Equivalences between tactics in HOL4 and Coq

Some approximate equivalences between HOL4 and Coq tactics.
Note that some may not be true equivalences but they can just be used in similar ways.

| Coq                      | HOL4                                      | Comment                       | Link                                        |
|--------------------------|-------------------------------------------|-------------------------------|---------------------------------------------|
| `apply` _thm_            | `drule`/`irule`/`match_mp_tac` _thm_      |                               |                                             |
| `apply` _asm_            | `first_assum match_mp_tac`                | Or similar tactical or tactic |                                             |
| `apply` _thm_ `in` _asm_ | `imp_res_tac` _thm_                       |                               |                                             |
| `apply` _asm_ `in` _asm_ | `res_tac`                                 |                               |                                             |
| `subst`                  | `rveq` (from CakeML preamble)             |                               |                                             |
| `specialize`             | `qspecl_then`                             |                               |                                             |
| `eexists`                | `asm_exists_tac` (from CakeML preamble)   | Weak correspondence           |                                             |
| `rewrite`                | `once_rewrite_tac`, `rewrite_tactic`, ... |                               |                                             |
| `simpl in *`             | `fs`                                      |                               |                                             |
| `auto`                   | `rw`                                      | Weak correspondence           |                                             |
| `destruct`               | `Cases`, `Cases_on`, `PairCases_on`       |                               |                                             |
| `induction`              | `Induct`, `Induct_on`                     |                               |                                             |
| `intros`                 | `rpt strip_tac`                           | `strip_tac` does more         |[IntroductionTactics](IntroductionTactics.md)|

## Assumption handling

When introducing a new assumption in a proof in Coq it is either named automatically or
given a name explicitly by the user. This name is later used when referring to the assumption.
For example, applying the assumption `H` to the goal is done by

    apply H

Similarly, applying the assumption `H` in the assumption `H0` is done by

    apply H in H0

In HOL4 assumptions are instead referred to by position or pattern. For example, `pop_assum`
applies a tactic generated from the first assumption. The tactical `first_assum` works similarly,
but instead iterates over the assumptions and applies the first successful (generated) tactic.

The tactical `qpat_assum` can be used to pick out assumptions based on a pattern instead of position.

In Coq assumptions can be picked out by patterns using the `match` construct in Ltac. This proof-style
is advocated, over name-based assumption handling, in e.g. ''Certified Programming with Dependent Types''.

## Automation and subgoals

The handling of subgoals is different in Coq and HOL4.

In Coq, when using a lemma or a hypothesis of the form `! x. P x ==> Q x` where `Q x` that does not prove the current goal immediately, one can either use the tactics
Coq will always generate a subgoal for each left-hand side of an implication occurring on P x.

HOL4 would require doing a sub-proof using `by` to obtain the conclusion `Q x`.

If desired, it is possible to mimic the behavior of HOL4 in Coq using the `assert` tactic, that allows to explicitly introduce subgoals.
In the same style, one can mimic the behavior of Coq in HOL4 using

```
fun impl_subgoal_tac th =
  let
      val hyp_to_prove = lhand (concl th)
  in
      SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end
```

Note that the tactic requires all free variables (under a forall quantification) to be instantiated.

## Proof-style

HOL4 proofs are more "batch-style", meaning that a proof is either solved or not by a tactic and there is no explicit proof mode as in Coq.
Hence the interactive proof-mode is separated from the actual saving of a proven theorem.

In contrast, Coq has a separate proof-mode, that can be started after stating a theorem.
This allows for easily stepping through proofs by just following the structure of the input file.

## Foundational differences

The underlying logic in Coq is constructive and based on the type theory the calculus of (co)inductive
constructions (CIC). The system is based on the Curry–Howard isomorphism, and the language is dependently typed.
Classical reasoning can be recovered by importing `Coq.Logic.Classical`.

HOL4 is instead based on a variant of Church's simple theory of types (a classical higher-order logic).
The system uses the LCF-approach with a `thm` structure to ensure that all theorems in the system are
derived from a small set of inference rules.

Coq is implemented in OCaml, but this fact is hidden from its users (as long as they do not write plugins).
Whereas Coq users are exposed to Gallina, "The vernacular", and Ltac, HOL4 users are instead directly
exposed to the system's implementation language: Standard ML.
