# Equivalences between tactics in HOL4 and Coq

_This is a work in progress, pull requests and comments more than welcome._

Some approximate equivalences between HOL4 and Coq tactics.
Note that some may not be true equivalences but they can just be used in similar ways.

| Coq                      | HOL4                                      | Comment                                  | Link                                        |
|--------------------------|-------------------------------------------|------------------------------------------|---------------------------------------------|
| `apply` _thm_            | `drule`/`irule`/`match_mp_tac` _thm_      |                                          |                                             |
| `apply` _asm_            | `first_assum match_mp_tac`                | Or similar tactical or tactic            |                                             |
| `apply` _thm_ `in` _asm_ | `imp_res_tac` _thm_                       |                                          |                                             |
| `apply` _asm_ `in` _asm_ | `res_tac`                                 |                                          |                                             |
| `subst`                  | `rveq` (from CakeML preamble)             |                                          |                                             |
| `specialize`             | `qspecl_then`                             |                                          |                                             |
| `eexists`                | `asm_exists_tac` (from CakeML preamble)   | Weak correspondence                      |                                             |
| `rewrite`                | `once_rewrite_tac`, `rewrite_tactic`, ... |                                          |                                             |
| `simpl in *`             | `fs`                                      |                                          |                                             |
| `auto`                   | `metis_tac`, `rw`                         | Weak correspondence                      |                                             |
| `destruct`               | `Cases`, `Cases_on`, `PairCases_on`       |                                          |                                             |
| `induction`              | `Induct`, `Induct_on`                     | subtle differences (e.g. rule induction) |[InductionTactics](InductionTactics.md)      |
| `intros`                 | `rpt strip_tac`                           | `strip_tac` does more                    |[IntroductionTactics](IntroductionTactics.md)|
| `split`                  | `EQ_TAC`                                  | `split` can also split other connectives |                                             |

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
is advocated, over name-based assumption handling, in e.g. _Certified Programming with Dependent Types_.

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

_TODO: Isn't this simply a property of particular GUIs (Proof General vs. the Emacs mode for HOL4) rather than the actual ITPs?_

## Formalization styles

One minor difference between Coq and HOL4 is how theorems with multiple hypotheses are written. In Coq we would write,

    (P -> Q) -> (Q -> P) -> (P <-> Q)

whereas in HOL4 we would write

    (P ==> Q) /\ (Q ==> P) ==> (P = Q)

This, as far as I know, is just a stylistic difference.

## Proof by reflection/computation

In Coq, so-called proofs by reflection are (seemingly) common. For clarity, this is sometimes called "computational reflection" to differentiate it from other forms of reflection.
For example, in Coq, we have the the Mathematical Components (ssreflect) library. Also, simply Googeling for "reflection coq" results in many relevant hits.

Two reflection tutorials for Coq: [Speeding Up Proofs with Computational Reflection](https://gmalecha.github.io/reflections/2017/speeding-up-proofs-with-computational-reflection) (2017)
and [Proofs by Reflection, Tactic Language](https://www.lri.fr/~paulin/MPRI/cours-refl.pdf) (2011).

To automate the lifting of the goal to "syntax" one can use either Ltac or write a specialized plugin (in OCaml) in Coq, whereas in HOL4 one would do this in SML directly.
Harrison has done a comparison of reflection in the Coq and HOL: [Computation and reflection in Coq and HOL](http://www.cl.cam.ac.uk/~jrh13/slides/nijmegen-20aug03/slides.pdf) (2003).
Reduction in HOL4 is not at fast as in Coq, see the slides for details. (Isabelle/HOL has "support" for reflection, where reductions can be made fast by translating terms to SML for compilation.
But how do they automate the lift to syntax?)

_TODO: Port some reflection example written in Coq to HOL4 as an illustration. E.g. Chlipala's example from the DeepSpec summer school._

## Metavariables

Coq has metavariables (introduced by e.g. `eapply` or `eexists`). HOL4 does not have a corresponding concept. (Isabelle/HOL has "schematic variables".)

## Type classes

Coq has type classes (in the same way as in e.g. Haskell). HOL4 has not. (Isabelle/HOL has.)

In some cases there are workarounds for this. For example, do-syntax is available for monomorphized monads. See e.g. `candle/standard/monadic/holKernelProofScript.sml` from CakeML.
But you still have to duplicate monad theorems and functions, but at least you get the syntax.

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
