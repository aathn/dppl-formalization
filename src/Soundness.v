From TLC Require Import LibEnv LibTactics.
From Coq Require Import Reals.
From DPPL Require Import Syntax Typing Eval.

Theorem eval_deterministic_det :
  forall t1 t2 t2',
    t1 -->d t2 ->
    t1 -->d t2' ->
    t2 = t2'.
Proof.
Admitted.

Lemma progress_const_eval :
  forall c T1 T2 v m,
  const_type c = (T1, T2) ->
  value v ->
  empty |= v ~: m, T1 ->
  exists v',
    const_eval c v = Some v'.
Proof.
  introv Hconsttype Hvalue Htype.
  destruct c ; inverts Hconsttype.
  destruct Hvalue ; inverts Htype as Htype1 Htype2.
  - destruct Hvalue1 ; inverts Htype1 as Hconsttype1.
    destruct Hvalue2 ; inverts Htype2 as Hconsttype2.
    exists (TmReal (r + r0)). reflexivity.
Qed.

Theorem progress_det :
  forall t T,
    empty |= t ~: Det, T ->
    value t \/ exists t', t -->d t'.
Proof.
  introv Htype. remember empty as Gamma. remember Det as m.
  induction Htype ; subst.
  - apply binds_empty_inv in H. destruct H.
  - left. apply VLam.
  - right. destruct IHHtype1 as [Hvalue1 | (t1' & Hstep1)] ; try reflexivity.
    + destruct IHHtype2 as [Hvalue2 | (t2' & Hstep2)] ; try reflexivity.
      * inverts Htype1 as Hconst ; inverts Hvalue1.
        { exists ([0 ~> t2]t). apply EApp. apply Hvalue2. }
        { destruct (progress_const_eval _ _ _ _ _ Hconst Hvalue2 Htype2)
            as (v' & Hconst_some).
          exists v'. apply EConstApp. apply Hvalue2. apply Hconst_some. }
      * exists (TmApp t1 t2'). apply ECongD. apply ECAppR. apply Hvalue1. apply Hstep2.
    + auto_star.
  - left. apply VReal.
  - left. apply VConst.
  - left. apply VUnit.
  - destruct IHHtype1 as [Hvalue1 | (t1' & Hstep1)] ; try reflexivity.
    + destruct IHHtype2 as [Hvalue2 | (t2' & Hstep2)] ; try reflexivity.
      * left. apply VPair.
        { apply Hvalue1. }
        { apply Hvalue2. }
      * right*.
    + right*.
  - destruct IHHtype as [Hvalue | (t' & Hstep)] ; try reflexivity.
    + right. inverts Htype ; inverts Hvalue. exists (t1). apply EFst ; assumption.
    + right*.
  - destruct* IHHtype as [Hvalue | (t' & Hstep)].
    inverts Htype ; inverts* Hvalue.
  - destruct IHHtype1 as [Hvalue1 | (t1' & Hstep1)] ; try reflexivity.
    + right. inverts Htype1 ; inverts Hvalue1. destruct (Rle_or_gt r 0).
      * exists t3. apply EIfFalse. assumption.
      * exists t2. apply EIfTrue. assumption.
    + right*.
  - destruct IHHtype as [Hvalue | (t' & Hstep)] ; try reflexivity.
    + left. apply VDist. assumption.
    + right. exists (TmDist d t'). apply ECongD. apply ECDist. apply Hstep.
  - discriminate.
  - discriminate.
Qed.

Theorem preservation_det :
  forall Gamma t t' T m,
    Gamma |= t ~: m, T ->
    t -->d t' ->
    Gamma |= t' ~: m, T.
Proof.
  introv Htype Hstep. gen T.
  induction Hstep ; intros.
  - admit.
  - admit.
  - inverts Htype. assumption.
  - inverts Htype. assumption.
  - inverts Htype as Htype'. inverts Htype'. assumption.
  - inverts Htype as Htype'. inverts Htype'. assumption.
  - inverts H ; inverts* Htype.
    admit.
Admitted.

