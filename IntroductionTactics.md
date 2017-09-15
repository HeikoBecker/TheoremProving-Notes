# Introduction Tactics

Both in Coq and HOL4, what is referred to by "introduction" corresponds to forall quantifier and implication introduction.

Forall quantifier introduction refers to moving universally quantified variable into the context:

```
  x:T |- P x
  ----------
   |- ∀ (x:T). P x
```

Implication introduction refers to moving the left-hand side of an implication into the context:

```
  𝚺;P |- Q
  ---------
  𝚺 |- P ==> Q
```

In Coq, both of these rules are handled with the `intros` tactic.
In HOL4, forall elimination can be handled with `gen_tac` and implication elimination with `disch_then assume_tac`.
To handle both rules at once, HOL4 also has the stronger `strip_tac` tactic.

Writing theorems in a curried style (`∀ x. P x ==> Q x ==> R x`), these tactics have the very same behavior.

Both provers can also deal with the same theorem in its uncurried form (`∀ x. P x /\ Q x ==> R x`).

In HOL4, `strip_tac` will automatically apply conjunction elimination to `P x /\ Q x`.
In Coq, `intros * [H1 H2]` will automatical apply conjunction elimination too, introducing the hypothesis `H1: P x` and `H2: Q x`.