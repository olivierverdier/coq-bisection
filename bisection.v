Require Import Coq.Reals.Reals.


Local Open Scope R_scope.


Record BisectData := mkBisectData {
                         lft : R;
                         rgt : R
                               }.

Definition mid (a:R) (b:R) : R :=
  (a + b)/2.

(* Funny definition of bisect using Coq tactics *)

Definition bisect (f: R -> R) (d: BisectData) : BisectData.
Proof.
  destruct d as [a b].
  pose (c := mid a b).
  pose (fc := f c).
  pose (isneg := Rle_lt_dec fc 0).
  pose (da := mkBisectData  c b).
  pose (db := mkBisectData  a c).
  destruct isneg.
  *
     apply da.
  *
     apply db.
Defined.

(* A more standard definition: *)

Print bisect.

(* The bisection step leaves the following property invariant *)

Definition isAdmissible (f: R -> R) (d: BisectData) : Prop :=
  let a := lft d in
  let b := rgt d in 
 (a <= b) /\ (f a <= 0) /\ (0 <= f(b)).

Definition width (d: BisectData) : R := (rgt d) - (lft d).


(* Main Lemma: forall a b: R, (a <= b) -> a <= mid a b <= b. *)

(* we need some preliminary results first *)

Lemma compat_mid_le : forall a b c d : R, a + b <= c + d -> mid a b <= mid c d.
Proof.
  intros. 
  unfold mid. apply Rmult_le_compat_r. auto with real. exact H.
Qed.
  
Lemma mid_mid': forall a b: R, (a <= b) -> mid a a <= mid a b <= mid b b.
Proof.
  intros a b a_le_b.
  split; apply compat_mid_le; auto with real.
Qed.

Lemma mid_xx : forall a: R, mid a a = a.
Proof.
  intros. unfold mid. rewrite Rdiv_plus_distr; rewrite double_var; reflexivity.
Qed.

Lemma mid_mid: forall a b: R, (a <= b) -> a <= mid a b <= b.
Proof.
  intros a b H. apply mid_mid' in H; repeat rewrite mid_xx in H. exact H.
Qed.
   
(* Main Theorem: properties of one step of bisection
The statement speaks for itself, but it means that
- the left side increases
- the right side decreases
- the width is divided by two
- the new interval is also admissible

The proof is long but trivial. It is just a case analysis on whether or not f((a+b)/2) is positive, and repetitive use of the mid_mid Lemma.

 *)

Theorem main : forall d f, (isAdmissible f d) ->
                                lft d <= lft (bisect f d)
                                /\
                                rgt (bisect f d) <= rgt d
                                /\
                                width (bisect f d) = (width d)/2
                                /\
                                isAdmissible f (bisect f d).
Proof.
  intros.
  destruct d as [a b].
  destruct H as [a_le_b Hf].
  destruct Hf as [Hfa Hfb].
  simpl.
  case (Rle_lt_dec (f (mid a b)) 0).

  * (* f(c) <= 0 *)
    intros fneg. simpl. split.
  - (* a <= mid a b *)
    apply mid_mid. apply a_le_b.
  - (*b <= b /\ mid a b <= b /\ f (mid a b) <= 0 <= f b *)
    split.
        + (*b <= b *)
          simpl.  apply Rle_refl.
        + (* mid a b <= b /\ f (mid a b) <= 0 <= f b *)
         split.
         (* half *)
         unfold mid. unfold width. simpl. field_simplify. reflexivity.
         split.
         (* mid a b <= b *)
           apply mid_mid. apply a_le_b.
           (* f (mid a b) <= 0 <= f b *)
           split.
           (* f (mid a b) <= 0 *)
           apply fneg.
           (* 0 <= f b *)
           apply Hfb.

  
    * (* f(c) > 0 *) (* same as above*)
           intros fpos.
    split.

    simpl. apply Rle_refl.

    split.

    simpl. apply mid_mid. apply a_le_b.

    split.

    simpl. unfold mid. unfold width. simpl. field_simplify. reflexivity.

    unfold isAdmissible. split.

    apply mid_mid. apply a_le_b.
    
    split. apply Hfa. apply Rlt_le. apply fpos.
Qed.

(* The left side is bounded by the previous right side
 it is used to get a global bound for the left sides *)

Ltac ov := try apply main; eassumption.

Lemma lftBound: forall d f, (isAdmissible f d) -> lft (bisect f d) <= rgt d.
Proof.
  intros.
  apply main with (d:=d) (f:=f) in H.  
  apply Rle_trans with (r2:=rgt(bisect f d)); apply H.
Qed.
  

(* Define the actual sequence of iterated applications of bisect *)


Fixpoint sequence (f: R -> R) (d: BisectData) (n: nat) : BisectData :=
  match n with
    | O => d
    | S n => bisect f (sequence f d n)
    end.

Definition lfts (u: nat -> BisectData)  (n: nat) : R :=
  lft (u n).

Definition rgts (u: nat -> BisectData) (n: nat) : R :=
  rgt (u n).

(* all the intervals at all steps are admissible *)

Lemma allAdmissible: forall d f, (isAdmissible f d) -> forall n, isAdmissible f (sequence f d n).
Proof.
  intros.
  induction n.
  * apply H.
  * ov.
Qed.

(* Not powerful enough yet; we want a tactic which does
      apply main; apply allAdmissible?
*)
Hint Resolve allAdmissible.
Hint Resolve main.

Print Hint *.
(* Change Ltac ov to apply main. apply allAdmissible? Or use match goal...? *)
Ltac ov ::= try apply main; try apply allAdmissible; eassumption.

(* the left sides make an increasing sequence *)

Lemma lfts_grow : forall d f, (isAdmissible f d) -> Un_growing (lfts (sequence f d)).
Proof.
  intros.
  unfold Un_growing.
  intros.
  unfold lfts. ov.
Qed.

(* the right sides have a common bound *)

Lemma rgt_bound: forall f d, isAdmissible f d -> forall n, rgt (sequence f d n) <= rgt d.
Proof.
  intros.
  induction n as [|n'].
  *
    simpl. apply Rle_refl.
  *
    simpl.    
    assert (Hi: rgt  (bisect f (sequence f d n')) <= rgt  (sequence f d n')).
    ov.
    apply Rle_trans with (r2:= rgt  (sequence f d n')). apply Hi. apply IHn'.
Qed.

(* left sides are lower than right sides *)

Lemma lft_rgt: forall f d, (isAdmissible f d) -> forall n, lft (sequence f d n) <= rgt (sequence f d n).
Proof.
  intros. apply allAdmissible with (n:=n) in H. apply H.
Qed.

(* common bound for the left sides *)

Lemma lfts_bound': forall f d, (isAdmissible f d) -> forall n, lft (sequence f d n) <= rgt d.
Proof.
  intros.
  apply Rle_trans with (r2:= rgt (sequence f d n)).
  apply lft_rgt. apply H. apply rgt_bound. apply H.
Qed.


(* left sides is bounded (using Coq's definition) *)

Lemma lfts_bound : forall f d, (isAdmissible f d) -> bound (EUn (lfts (sequence f d))).
Proof.
  intros.
  unfold bound.
  exists (rgt d).
  unfold is_upper_bound. unfold EUn. unfold lfts.
  intros x HE.
  destruct HE as [n HH]. rewrite HH. apply lfts_bound'. apply H.
Qed.

  
  
(* the left sides converge, because it is an increasing, bounded sequence *)


Lemma lfts_conv : forall f d, (isAdmissible f d) -> exists l : R, Un_cv (lfts (sequence f d)) l.
Proof.
  intros.
  apply Un_cv_crit. apply lfts_grow. apply H. apply lfts_bound. apply H.
Qed.

(* the value of f at the left sides is always nonpositive *)

Lemma lft_fneg: forall f d, (isAdmissible f d) -> forall n, f (lft (sequence f d n)) <= 0.
Proof.
  intros. apply allAdmissible with (n:=n) in H. apply H.
Qed. 

Lemma rgt_fpos: forall f d, (isAdmissible f d) -> forall n, 0 <= f (rgt (sequence f d n)).
Proof.
  intros. apply allAdmissible with (n:=n) in H. apply H.
Qed.

Definition half_power (n:nat) : R := /2^n.


Lemma hp: forall n, half_power n / 2 = half_power (S n).
Proof.
  intros.
  unfold half_power.
  simpl. field_simplify. reflexivity.

  apply pow_nonzero.
  assert (2 = INR 2).
  auto with real.
  rewrite H. auto with real.

  apply pow_nonzero.
  assert (2 = INR 2).
  auto with real.
  rewrite H. auto with real.
Qed.

Lemma triv_associative: forall x y, x * y /2 = x * (y /2).
Proof.
  intros.
  field_simplify.
  reflexivity.
Qed.

Lemma width_half_power: forall f d,
                          (isAdmissible f d)
                          -> forall n, width (sequence f d n)  = width d * half_power n.
Proof.
  intros.
  unfold width.
  induction n as [|n'].
  simpl.  assert (Hhp0: half_power 0 = 1). unfold half_power. auto with real. rewrite Hhp0. auto with real.
  simpl. assert (Hadn: isAdmissible f (sequence f d n')). apply allAdmissible. apply H.
  apply main in Hadn. destruct Hadn as [Hl [Hr [Hw Hd]]].  unfold width in Hw. rewrite IHn' in Hw. rewrite Hw.
  assert (Hhp: (rgt d - lft d) * (half_power n' / 2) = ((rgt d - lft d) * (half_power (S n')))).
  rewrite hp. reflexivity.
  assert (Hass: (rgt d - lft d) * half_power n' / 2 = (rgt d - lft d) * (half_power n' / 2)). apply triv_associative.
  rewrite Hass. 
  rewrite Hhp. reflexivity.
Qed.  
               

Lemma half_power_cv_0: forall x, Un_cv (fun n:nat => x * half_power n) 0.
Admitted.

Require Export Coq.Logic.FunctionalExtensionality.

Lemma width_cv_0: forall f d, (isAdmissible f d) ->
                         Un_cv (fun n => width (sequence f d n)) 0.
Proof.
  intros.
  assert ((fun n:nat => width (sequence f d n)) = (fun n:nat => (width d) * half_power n)).
  apply functional_extensionality.
  intros.
  rewrite width_half_power. reflexivity. apply H. rewrite H0. 
  apply half_power_cv_0.
Qed.

Lemma both_cv: forall f d,
                 (isAdmissible f d) ->
                 exists l,
                    Un_cv (lfts (sequence f d)) l
                    /\
                    Un_cv (rgts (sequence f d)) l.
Proof.
  intros.
  pose (Hcv':= lfts_conv f d H).
  destruct Hcv' as [lim Hcv].
  exists lim.
  split.
  *
  assumption.
  *
  unfold rgts.
  assert (Hwidth: forall x, rgt x = lft x + width x).
  intros.
  unfold width. auto with real.
  assert (Hw: forall n,  rgt (sequence f d n) = lft (sequence f d n) + width (sequence f d n)).
  intros. apply Hwidth.
  assert (Un_cv (fun n:nat => lft (sequence f d n) + width (sequence f d n)) lim).
  pose (Hw0:= width_cv_0 f d H).
  pose (Hcv_plus:= CV_plus (lfts (sequence f d)) (fun n => width (sequence f d n)) lim 0 Hcv Hw0).
  assert (lim0: lim = lim + 0).
  auto with real.
  rewrite lim0.
  apply Hcv_plus.
  assert ((fun n : nat => rgt (sequence f d n)) = (fun n:nat => (lft (sequence f d n) + width (sequence f d n)))).
  apply functional_extensionality.
  intros.
  apply Hw.
  rewrite H1.
  apply H0.
Qed.

  


  

(* the following should be part of some standard library,
but I could not find it *)

Lemma f_cont_le: forall f u l,
                      (continuity_pt f l) ->
                      (Un_cv u l) ->
                      (forall n, f(u n) <= 0) ->
                      f l <= 0.
Admitted.

Lemma f_cont_ge: forall f u l,
                      (continuity_pt f l) ->
                      (Un_cv u l) ->
                      (forall n, 0 <= f(u n)) ->
                      0 <= f l.
Admitted.


Lemma le_eq: forall x:R, 0 <= x -> x <= 0 -> x = 0.
Admitted.


Theorem Final: forall f d,
                   (isAdmissible f d) ->
                   (continuity f) ->
                   exists l,
                     Un_cv (lfts (sequence f d)) l
                     /\
                     f(l) = 0.
Proof.
  intros.
  pose (both_cv f d H).
  destruct e as [lim [Hcvl Hcvr]].

  exists lim.
  split.
  exact Hcvl.

  assert (f lim <= 0).
  apply f_cont_le with (u := lfts (sequence f d)). apply H0. apply Hcvl. apply lft_fneg. apply H.

  assert (0 <= f lim).
  apply f_cont_ge with (u := rgts (sequence f d)).
  apply H0.
  apply Hcvr.
  apply rgt_fpos. apply H.
  apply le_eq.
  apply H2.
  apply H1.
Qed.
  

    


  
(*
Remains to be done: 
  - Proof of the admitted results above
  - Extract the bisection algorithm to Haskell
*)