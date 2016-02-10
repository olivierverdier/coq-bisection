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
  match d with
    | mkBisectData a b => (a <= b) /\ (f a <= 0) /\ (0 <= f(b))
     end.


Definition width (d: BisectData) : R :=
  match d with
    | mkBisectData a b => b - a
end.


(* Main Lemma: forall a b: R, (a <= b) -> a <= mid a b <= b. *)

(* we need some preliminary results first *)


Lemma one_half: 0 <= (/2).
Proof.
  assert (two_ge_0: 0 < INR 2).
  apply lt_0_INR.
  auto.
  assert (two_two: INR 2 = 2). simpl. reflexivity.
  assert (two_gt_0: 0 < 2). rewrite <- two_two. apply two_ge_0.
  assert (half_gt_0: 0 < /2). refine (Rinv_0_lt_compat _ _). apply two_gt_0.
  apply Rlt_le. apply half_gt_0.
Qed.

Lemma compat_mid_le : forall a b c d : R, a + b <= c + d -> mid a b <= mid c d.
Proof.
  intros.
  unfold mid.
  assert (mul_half: (a+b)*(/2) <= (c+d)*(/2)). apply Rmult_le_compat_r. apply one_half.  
  apply H.
  assert (div_two_mul_half: forall x: R, x / 2 = x * (/2)). intros. field_simplify. reflexivity.
  assert (rwab: (a+b)/2 = (a+b)*(/2)). apply div_two_mul_half.
  assert (rwcd: (c+d)/2 = (c+d)*(/2)). apply div_two_mul_half.
  rewrite rwab. rewrite rwcd. apply mul_half.
Qed.



  
Lemma mid_mid': forall a b: R, (a <= b) -> mid a a <= mid a b <= mid b b.
Proof.
  intros a b a_le_b.
  split.
  *
    apply compat_mid_le. refine (Rplus_le_compat_l _ _ _ _). apply a_le_b.
  *
    apply compat_mid_le. refine (Rplus_le_compat_r _ _ _ _). apply a_le_b.
Qed.

Lemma mid_xx : forall a: R, mid a a = a.
Proof.
  intros. unfold mid. field_simplify. field_simplify. reflexivity.
Qed.

Lemma mid_mid: forall a b: R, (a <= b) -> a <= mid a b <= b.
Proof.
  intros a b a_le_b.
  split.
  *
    assert (rw: mid a a = a). apply mid_xx.
    assert (H: mid a a <= mid a b). apply mid_mid'. apply a_le_b.
    rewrite rw in H. apply H.
  *
    assert (rw: mid b b = b). apply mid_xx.
    assert (H: mid a b <= mid b b). apply mid_mid'. apply a_le_b.
    rewrite rw in H. apply H.
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
         unfold mid. field_simplify. reflexivity.
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

    simpl. unfold mid. field_simplify. reflexivity.

    unfold isAdmissible. split.

    apply mid_mid. apply a_le_b.

    split. apply Hfa. apply Rlt_le. apply fpos.
Qed.

(* The left side is bounded by the previous right side
 it is used to get a global bound for the left sides *)

Lemma lftBound: forall d f, (isAdmissible f d) -> lft (bisect f d) <= rgt d.
Proof.
  intros.
  assert (d'_ad: isAdmissible f (bisect f d)). apply main. apply H.
  assert (a_le_a': lft d <= lft (bisect f d)). apply main. apply H.
  assert (b'_le_b: rgt (bisect f d) <= rgt d). apply main. apply H.
  assert (a'_le_b': lft (bisect f d) <= rgt(bisect f d)). destruct (bisect f d) as [a' b'] eqn:eqd'. destruct d'_ad as [a'_le_b' Hf].
  simpl. apply a'_le_b'.
  apply Rle_trans with (r2:=rgt(bisect f d)). apply a'_le_b'. apply b'_le_b.
  Qed.

  

(* Define the actual sequence of iterated applications of bisect *)


Fixpoint sequence (f: R -> R) (d: BisectData) (n: nat) : BisectData :=
  match n with
    | O => d
    | S n => bisect f (sequence f d n)
    end.

Definition lfts (u: nat -> BisectData)  (n: nat) : R :=
  lft (u n).

(* all the intervals at all steps are admissible *)

Lemma allAdmissible: forall d f, (isAdmissible f d) -> forall n, isAdmissible f (sequence f d n).
Proof.
  intros.
  induction n.
  *
    simpl. apply H.
  *
    simpl. apply main. apply IHn.
Qed.

(* the left sides make an increasing sequence *)

Lemma lfts_grow : forall d f, (isAdmissible f d) -> Un_growing (lfts (sequence f d)).
Proof.
  intros.
  unfold Un_growing.
  intros.
  unfold lfts. simpl. apply main. apply allAdmissible. apply H.
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
    apply main. apply allAdmissible. apply H.
    apply Rle_trans with (r2:= rgt  (sequence f d n')). apply Hi. apply IHn'.
Qed.

(* left sides are lower than right sides *)

Lemma lft_rgt: forall f d, (isAdmissible f d) -> forall n, lft (sequence f d n) <= rgt (sequence f d n).
Proof.
  intros.
  assert (H_ad:isAdmissible f (sequence f d n)). apply allAdmissible. apply H.
  destruct (sequence f d n) as [a b]. destruct H_ad as [H_le Hf]. apply H_le.
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
  intros.
  assert (H_ad: isAdmissible f (sequence f d n)). apply allAdmissible. apply H.
  destruct (sequence f d n). destruct H_ad as [H_le Hf]. apply Hf.
Qed. 

Lemma rgt_fpos: forall f d, (isAdmissible f d) -> forall n, 0 <= f (rgt (sequence f d n)).
Proof.
  intros.
  assert (H_ad: isAdmissible f (sequence f d n)). apply allAdmissible. apply H.
  destruct (sequence f d n). destruct H_ad as [H_le H_f]. apply H_f.
Qed.
  
(*
Remains to be done: 
  - The right part converges (using the Lemma half), and has the same limit l as the left sides
  - Assume f continuous, and show that f(l) <= 0, f(l) >= 0, so f(l) = 0.
  - Extract the bisection algorithm to Haskell
*)