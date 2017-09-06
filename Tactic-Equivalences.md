# Equivalences between tactics in HOL4 and Coq

Some approximate equivalences between HOL4 and Coq tactics.
Note that some may not be true equivalences but they can just be used in similar ways.

| Coq                      | HOL4                                      | Comment                       |
|--------------------------|-------------------------------------------|-------------------------------|
| `apply` _thm_            | `drule`/`irule`/`match_mp_tac` _thm_      |                               |
| `apply` _asm_            | `first_assum match_mp_tac`                | Or similar tactical or tactic |
| `apply` _thm_ `in` _asm_ | `imp_res_tac` _thm_                       |                               |
| `apply` _asm_ `in` _asm_ | `res_tac`                                 |                               |
| `subst`                  | `rveq` (from CakeML preamble)             |                               |
| `specialize`             | `qspecl_then`                             |                               |
| `eexists`                | `asm_exists_tac` (from CakeML preamble)   | Weak correspondence           |
| `rewrite`                | `once_rewrite_tac`, `rewrite_tactic`, ... |                               |
| `simpl in *`             | `fs`                                      |                               |
| `auto`                   | `rw`                                      | Weak correspondence           |
| `destruct`               | `Cases`, `Cases_on`, `PairCases_on`       |                               |
| `induction`              | `Induct`, `Induct_on`                     |                               |
| `intros`                 | `rpt strip_tac`                           | `strip_tac` does more         |

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
