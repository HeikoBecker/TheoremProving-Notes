structure hol4_asmLib =
struct
open BasicProvers Defn HolKernel Parse Tactic bossLib;

(**
  Show that we can "curry" a theorem, giving us a representation similar to
  intuitionistic theorem provers as e.g. Coq or Agda, because this allows
  for easy applications of modus ponens on complex lemma statements for
  simplifications in forward proofs where assumptions should be manipulated
**)
fun curry_rule thm = REWRITE_RULE [GSYM AND_IMP_INTRO] thm;
fun uncurry_rule thm = REWRITE_RULE [AND_IMP_INTRO] thm;

(**
  Term specialization tactic
  This  tactic is the key ingredient for the library.
  Instead of either providing functionality of the MP rule or the SPEC/SPECL
  tacticals, it combines both into one tactical.

  spec_thm should be called with hyp, being a :thm that should be specialized,
  pat_thm being either a term which can be used to instantiate a universal
  quantifier, or a pattern for an assumption with which modus ponens should
  match for the theorem. cont_tac is a tactical that may only depend on a
  theorem parameter (e.g. ASSUME_TAC, match_mp_tac)
**)
fun spec_thm_general hyp pat_thm cont_tac =
  let
      (* try specialization of universal quantifier *)
      val new_thm = Q.SPEC pat_thm hyp in
      cont_tac new_thm
  end
  handle HOL_ERR msg =>
    qpat_assum pat_thm
      (fn asm =>
          let
              val curry_hyp = curry_rule hyp
              val MP_hyp = MP curry_hyp asm
          in
              cont_tac (uncurry_rule MP_hyp)
          end);

fun spec_thm pat_hyp pat_thm =
  qpat_assum pat_hyp
    (fn hyp =>
        spec_thm_general hyp pat_thm ASSUME_TAC);

(**
  List version of spec_term, specialization is done using the list,
  from left to right
**)
fun specialize_thm hyp pat_thm_list tac =
  case pat_thm_list of
      [] => tac hyp
    | pat_thm :: [] =>
      spec_thm_general hyp pat_thm tac
    | pat_thm :: ls =>
      spec_thm_general hyp pat_thm (fn thm => specialize_thm thm ls tac);

(* The actual specialization tactic is now just chaining together previously
defined tactics, still we make it parametric in the continuation **)
fun specialize pat_hyp pat_thm_list cont_tac =
  qpat_x_assum pat_hyp (fn asm => specialize_thm asm pat_thm_list cont_tac);

(** similarly, we can now build an apply tactic, similar to coq's apply **)
fun apply pat_hyp pat_thm_list =
  specialize pat_hyp pat_thm_list (fn thmres => (ACCEPT_TAC thmres) ORELSE (match_mp_tac thmres));

fun apply_thm thm pat_thm_list =
  specialize_thm thm pat_thm_list (fn thmres => (ACCEPT_TAC thmres) ORELSE (match_mp_tac thmres));

(**
  Pose proof allows to add a specialized version of the given theorem as a hypothesis
**)
fun pose_proof thm pat_term_list =
  specialize_thm thm pat_term_list ASSUME_TAC;

val my_match_mp_tac  = (fn thm => (fn gs => match_mp_tac thm gs))

fun simple_apply thm = (ACCEPT_TAC thm) ORELSE (match_mp_tac thm);

fun dumb_apply thm = (ACCEPT_TAC thm) ORELSE (FAIL_TAC "Unreachable");

(** Example for the use of spec_term/specialize **)
test val_thm = Q.prove (
  ` !(n:num) (P:num -> bool).
       P n ==>
       P n`,
  rpt gen_tac
      DISCH_THEN ASSUME_TAC
  qpat_x_assum `P n` (fn thm => simple_apply thm)
  qpat_x_assum `P n` (fn thm => dumb_apply thm)
  apply `P n` []
  specialize `!m. _ ==> _` [`n`, `n > 5`] (fn thm => simp [thm]));


(** TODO: Write mail. This is strange for the orelse behavior **)

(** Demonstration of pose proof **)
val _ = Q.prove (
  `!n. n < 5 ==> n < 6`,
  rpt strip_tac
  \\ `5 < 6` by (fs [])
  \\ apply_thm arithmeticTheory.LESS_TRANS [`n`,`5`, `6`,`n < 5`, `5 < 6`] (fn thm =>  (ACCEPT_TAC thm) ORELSE FAIL_TAC "WHOOPSIE");


(**
  more sophisticated rewriting tactic, for rewriting with assumptions
  second parameter is used to distinguish whether to rewrite only in the goal,
  in all assumptions or in a specific assumption
**)
fun rewrite_asm_tac (asm_pat:term quotation) (pos:term quotation) =
  qpat_x_assum asm_pat
    (fn asm =>
        (if (compare (Term pos, Term `_`) = EQUAL)
        then rw [asm]
        else
          (if (compare (Term pos, Term `goal`) = EQUAL)
            then rewrite_tac [asm]
            else qpat_x_assum `pos`
                   (fn asm' => ASSUME_TAC (REWRITE_RULE [asm] asm'))))
            THEN ASSUME_TAC asm);
