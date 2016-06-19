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

  
Lemma mid_mid': forall a b: R, (a <= b) -> mid a a <= mid a b <= mid b b.
Proof.
  intros.
  split; apply Rmult_le_compat_r; auto with real.
Qed.

Lemma mid_xx : forall a: R, mid a a = a.
Proof.
  intros. unfold mid. field. 
Qed.

Lemma mid_mid: forall a b: R, (a <= b) -> a <= mid a b <= b.
Proof.
  intros ? ? H. apply mid_mid' in H. repeat rewrite mid_xx in H. assumption.
Qed.
   
(* Main Theorem: properties of one step of bisection
The statement speaks for itself, but it means that
- the left side increases
- the right side decreases
- the width is divided by two
- the new interval is also admissible

The proof is trivial. It is just a case analysis on whether or not f((a+b)/2) is positive, and repetitive use of the mid_mid Lemma.

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
  intros [a b] f [a_le_b ?].
  apply mid_mid in a_le_b.
  simpl.
  simpl in a_le_b. destruct a_le_b.
  case (Rle_lt_dec (f (mid a b)) 0); repeat split; intuition; unfold mid, width; simpl; try field; auto with real.
Qed.

(* The left side is bounded by the previous right side
 it is used to get a global bound for the left sides *)

Ltac ov := try apply main; eassumption.

Lemma lftBound: forall d f, (isAdmissible f d) -> lft (bisect f d) <= rgt d.
Proof.
  intros d f ?.
  apply Rle_trans with (r2:=rgt(bisect f d)); apply main; assumption.
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
  intros ? ? ? n.
  induction n; try apply main; assumption.
Qed.


(* Change Ltac ov to apply main. apply allAdmissible? Or use match goal...? *)
Ltac ov ::= try apply main; try apply allAdmissible; eassumption.

(* the left sides make an increasing sequence *)

Lemma lfts_grow : forall d f, (isAdmissible f d) -> Un_growing (lfts (sequence f d)).
Proof.
  unfold Un_growing, lfts.
  intros. 
  apply main. auto using allAdmissible.
Qed.

(* the right sides have a common bound *)

Lemma rgt_bound: forall f d, isAdmissible f d -> forall n, rgt (sequence f d n) <= rgt d.
Proof.
  intros ? ? ? n.
  induction n as [|n']; auto with real.
  apply Rle_trans with (r2:= rgt  (sequence f d n')); try apply main; auto using allAdmissible.
Qed.

(* left sides are lower than right sides *)

Lemma lft_rgt: forall f d, (isAdmissible f d) -> forall n, lft (sequence f d n) <= rgt (sequence f d n).
Proof.
  intros. apply allAdmissible. assumption.
Qed.

(* common bound for the left sides *)

Lemma lfts_bound': forall f d, (isAdmissible f d) -> forall n, lft (sequence f d n) <= rgt d.
Proof.
  intros f d ? n.
  apply Rle_trans with (r2:= rgt (sequence f d n)); auto using lft_rgt, rgt_bound.
Qed.


(* left sides is bounded (using Coq's definition) *)

Lemma lfts_bound : forall f d, (isAdmissible f d) -> bound (EUn (lfts (sequence f d))).
Proof.
  intros ? d ?.
  unfold bound,is_upper_bound, EUn, lfts.
  exists (rgt d).
  intros ? [? HH].
  rewrite HH. apply lfts_bound'. assumption.
Qed.

  
  
(* the left sides converge, because it is an increasing, bounded sequence *)


Lemma const_cv: forall x, Un_cv (fun n => x) x.
Proof.
  unfold Un_cv. intros.
  exists 0%nat. intros _ _. unfold R_dist.
  rewrite Rminus_diag_eq; [|trivial].
  rewrite Rabs_R0. trivial.
Qed.


Lemma lfts_conv : forall f d, (isAdmissible f d)
                         -> exists l : R, Un_cv (lfts (sequence f d)) l
                                    /\
                                    lft d <= l <= rgt d.
Proof.
  intros f d H.
  assert (H0: exists l : R, Un_cv (lfts (sequence f d)) l).
  apply Un_cv_crit; auto using lfts_grow, lfts_bound.
  destruct H0 as [l Hcv].
  exists l.
  split; trivial.
  split.
  -
  replace d with (sequence f d 0); [|trivial].
  apply (growing_ineq (lfts (sequence f d)) l (lfts_grow d f H) Hcv 0).
  -
  apply Rle_cv_lim with (Un:=(lfts(sequence f d))) (Vn:=(fun k => rgt d)); trivial.
  apply lfts_bound'. assumption. apply const_cv.
Qed.

(* the value of f at the left sides is always nonpositive *)

Lemma lft_fneg: forall f d, (isAdmissible f d) -> forall n, f (lft (sequence f d n)) <= 0.
Proof.
  intros. apply allAdmissible. assumption.
Qed. 

Lemma rgt_fpos: forall f d, (isAdmissible f d) -> forall n, 0 <= f (rgt (sequence f d n)).
Proof.
  intros. apply allAdmissible. assumption.
Qed.

Definition half_power (n:nat) : R := /2^n.


Lemma hp: forall n, half_power n / 2 = half_power (S n).
Proof.
  intros.
  unfold half_power.
  simpl. field.
  apply pow_nonzero. discrR.
Qed.

Lemma width_half_power: forall f d,
                          (isAdmissible f d)
                          -> forall n, width (sequence f d n)  = width d * half_power n.
Proof.
  intros f d ? n.
  induction n as [|n' IHn'].
  * simpl.  unfold half_power. field. 
  * rewrite <- hp. simpl.
    assert (Hw: width (bisect f (sequence f d n')) = width (sequence f d n') / 2).
    + apply main. apply allAdmissible. assumption.
    + rewrite Hw. rewrite IHn'. field.
Qed.  
               



Lemma width_cv_0: forall f d, (isAdmissible f d) ->
                         Un_cv (fun n => width (sequence f d n)) 0.
Proof.
  intros f d ?.
  refine (Un_cv_ext (fun n => (width d) * half_power n) (fun n => width (sequence f d n)) _ 0 _).
  * symmetry. apply width_half_power. trivial.
  * apply cv_pow_half.
Qed.

Lemma both_cv: forall f d,
                 (isAdmissible f d) ->
                 exists l,
                    Un_cv (lfts (sequence f d)) l
                    /\
                    Un_cv (rgts (sequence f d)) l
                    /\
                    lft d <= l <= rgt d.
Proof.
  intros f d H.
  destruct (lfts_conv f d H) as [lim [Hcv [Hlel Hler]]].
  exists lim.
  repeat split; trivial.
  Check Un_cv_ext.
  refine (Un_cv_ext
                (fun n:nat => (lft (sequence f d n) + width (sequence f d n)))
                (rgts (sequence f d))
                _
                lim
                _).
  * unfold width, rgts. auto with real.
  * replace lim with (lim+0); [ | auto with real].
    refine (CV_plus (lfts (sequence f d)) (fun n => width (sequence f d n)) lim 0 _ _); auto using width_cv_0.
Qed.

  

Hint Resolve continuity_seq const_cv : cont_const.

Lemma f_cont_le: forall f u l,
                      (continuity_pt f l) ->
                      (Un_cv u l) ->
                      (forall n, f(u n) <= 0) ->
                      f l <= 0.
Proof.
  intros f u ? ? ? ?.
  apply Rle_cv_lim with (fun n => f (u n)) (fun n => 0); auto with cont_const.
Qed.
  

Lemma f_cont_ge: forall f u l,
                      (continuity_pt f l) ->
                      (Un_cv u l) ->
                      (forall n, 0 <= f(u n)) ->
                      0 <= f l.
Proof.
  intros f u ? ? ? ?.
  apply Rle_cv_lim with (fun n => 0) (fun n => f (u n)); auto with cont_const.
Qed.


Theorem Final: forall f d,
                   (isAdmissible f d) ->
                   (continuity f) ->
                   exists l,
                     Un_cv (lfts (sequence f d)) l
                     /\
                     lft d <= l <= rgt d
                     /\
                     f(l) = 0.
Proof.
  intros f d H ?.
  destruct (both_cv f d H) as [lim [Hcvl [Hcvr [Hlel Hler]]]].

  exists lim.

  repeat split; trivial.

  apply Rle_antisym; trivial.
  
  - apply f_cont_le with (u := lfts (sequence f d)); trivial.
    apply lft_fneg; trivial.
  - apply f_cont_ge with (u := rgts (sequence f d)); trivial.
    apply rgt_fpos; trivial.
Qed.

  
(* Extract the bisection algorithm to Haskell *)

Extraction Language Haskell.
Extraction "bisect.hs" sequence.