Add LoadPath "~/scratch/coq-8.2pl2/theories/LatticeLibrary/".
Require Import Bool FSets FSetDecide.
Require Import DecidableType SetIsType.
Require Signatures SolveWf.

(* The barebones minimum definition of a program analysis.
   The abstract domain is all one big lattice on (conceptually) finite sets of abstract states. *)
Module Abstract_HOFA (abs : Signatures.LatticeWf).
Import SolveWf.
Import abs.
Variable concrete : Type.
Variable alpha : concrete -> t.
(* Currently no use for gamma.

Variable gamma : abs.t -> Ensemble concrete.

Axiom abstraction_sound : forall a : abs.t, a = (joinoverall alpha (gamma a)).
Axiom concretization_sound : forall c : concrete, In concrete (gamma (alpha c)) c.
*)
Variable reduction : concrete -> concrete.
Variable reductionhat : t -> t.

Variable reductionhat_sound :
 forall c chat,
   (order (alpha c) chat) -> (order (alpha (reduction c)) (reductionhat chat)).

Variable reductionhat_monotone :
 forall chat chat', (order chat chat') -> (order (reductionhat chat) (reductionhat chat')).

Variable reductionhat_start : forall chat, order chat (reductionhat chat).


Module Import analysis_solution := SolveLeastFixPoint abs.
(* assumes bottom is the initial state. *)
Definition analysis (c : concrete) :
 {a : t | eq a (reductionhat a) /\ (exists n : nat, a = iter reductionhat n (alpha c))} :=
   (iter_fix reductionhat reductionhat_monotone (alpha c)) (reductionhat_start (alpha c)).

(* (lfp reductionhat reductionhat_monotone). *)

End Abstract_HOFA.

(* We factor out the set-wise lifting from the abstract reduction relation
   so definitions are more concise. An abstract state has multiple possible next states.
   Here we conceptualize the input lattice as being on the abstract states themselves.*)
Module Algorithmic_Reduction_HOFA (concrete : DecidableType) (abs : Signatures.LatticeWf).
  Print DecidableType.
 Module t_dec : DecidableType with Definition t := abs.t
                              with Definition eq := abs.eq
                              with Definition eq_refl := abs.eq_refl
                              with Definition eq_sym := abs.eq_sym
                              with Definition eq_trans := abs.eq_trans
                              with Definition eq_dec := abs.eq_dec.
  Definition t := abs.t.
  Definition eq := abs.eq.
  Definition eq_refl := abs.eq_refl.
  Definition eq_sym := abs.eq_sym.
  Definition eq_trans := abs.eq_trans.
  Definition eq_dec := abs.eq_dec.
 End t_dec.
 Module t_lift : WS with Module E := t_dec := FSetWeakList.Make t_dec.
 Parameter alpha : concrete.t -> abs.t.

 (* abs.t is the element type of the set t_lift.t *)

 Parameter reduction : concrete.t -> concrete.t.
 Parameter reductionhat : abs.t -> t_lift.t.

 Definition t_lift_union_fold (f : abs.t -> t_lift.t) (s : t_lift.t) : t_lift.t := t_lift.fold (fun elt s => (t_lift.union (f elt) s)) s t_lift.empty.

 Definition reductionhat_lift (s : t_lift.t) : t_lift.t := t_lift_union_fold reductionhat s.

 Definition alpha_lift (c : concrete.t) : t_lift.t := t_lift.singleton (alpha c).

 Definition order_lift (aset aset' : t_lift.t) : Prop :=
   forall a0, t_lift.In a0 aset -> exists a1, t_lift.In a1 aset' /\ abs.order a0 a1.

 Print abs.eq.

 Lemma order_cong1 : forall (x y z : t_dec.t), t_dec.eq x y -> ((abs.order x z) <-> (abs.order y z)).
 Proof.
   intros.
   split.

   rewrite H.
   intro x_le_z

 Lemma order_lift_cong1_rewrite : forall a b c, t_lift.Equal a b -> (order_lift a c <-> order_lift b c).
 Proof.
   intros a b c a_eq_b.
   split.
   intro a_le_c.
   unfold order_lift; intros a0 a0_in_b.
   apply a_eq_b in a0_in_b.
   apply a_le_c in a0_in_b; assumption.
   intro b_le_c.
   unfold order_lift; intros a0 a0_in_a.
   apply a_eq_b in a0_in_a.
   apply b_le_c in a0_in_a; assumption.
 Qed.
 Lemma order_lift_cong2_rewrite : forall a b c, t_lift.Equal b c -> (order_lift a b <-> order_lift a c).
 Proof.
   intros a b c b_eq_c.
   split.
   (* case 1 *)
   intro a_le_b.
   unfold order_lift; intros a0 a0_in_a.
   apply a_le_b in a0_in_a.
   destruct a0_in_a as [a1 conj].
   destruct conj as [a1_in_b a0_le_a1].
   apply b_eq_c in a1_in_b.
   exists a1; auto.
   (* case 2 *)
   intro a_le_c.
   unfold order_lift; intros a0 a0_in_a.
   apply a_le_c in a0_in_a.
   destruct a0_in_a as [a1 conj].
   destruct conj as [a1_in_c a0_le_a1].
   apply b_eq_c in a1_in_c.
   exists a1; auto.
 Qed.

 Lemma order_lift_cong1 : forall a b c, order_lift a c -> t_lift.Equal a b -> order_lift b c.
 Proof.
   intros a b c a_le_c a_eq_b.
   unfold order_lift, t_lift.Subset in a_le_c.
   unfold t_lift.Equal in a_eq_b.
   unfold order_lift, t_lift.Subset.
   intros a0 a0_in_b.
   apply a_eq_b in a0_in_b.
   apply a_le_c in a0_in_b; assumption.
 Qed.
 Lemma order_lift_cong2 : forall a b c, order_lift a b -> t_lift.Equal b c -> order_lift a c.
 Proof.
   intros a b c a_le_b b_eq_c.
   unfold order_lift, t_lift.Subset in a_le_b.
   unfold t_lift.Equal in b_eq_c.
   unfold order_lift, t_lift.Subset.
   intros a0 a0_in_a.
   apply a_le_b in a0_in_a.
   destruct a0_in_a as [a1 conj].
   destruct conj as [a1_in_b a0_le_a1].
   apply b_eq_c in a1_in_b.
   exists a1; auto.
 Qed.

 Parameter reductionhat_sound :
  forall (c : concrete.t) (chat : abs.t),
      (abs.order (alpha c) chat) ->
      exists2 chat',
        (abs.order (alpha c) chat') &
        (t_lift.In chat' (reductionhat chat)).

 Parameter reductionhat_monotone :
  forall chat chat', (abs.order chat chat') -> (order_lift (reductionhat chat) (reductionhat chat')).

(* TODO: Change to reachability *)
 Parameter reductionhat_start : forall chat, order_lift (t_lift.singleton chat) (reductionhat chat).

 Module t_lift_props := WProperties t_lift.

 Lemma none_in_empty : forall a, ~ t_lift.In a t_lift.empty.
 Proof.
   intros a i.
   apply t_lift.elements_1 in i.
   assert (t_lift.Empty t_lift.empty).
     exact t_lift.empty_1.
   assert (t_lift.elements t_lift.empty = nil).
     exact t_lift_props.elements_empty.
   rewrite H0 in i.
   inversion i.
 Qed.

 Lemma empty_subset_is_empty : forall s, t_lift.Subset s t_lift.empty -> t_lift.Equal s t_lift.empty.
   Proof.
     intros.
     apply t_lift_props.subset_cardinal in H.
     rewrite t_lift_props.empty_cardinal in H.
     remember (t_lift.cardinal s) as scard.
     assert (scard = 0).
     inversion H; auto.
     rewrite Heqscard in H0.
     assert (t_lift.Empty t_lift.empty).
       exact t_lift.empty_1.
     remember t_lift_props.cardinal_Empty as ecard.
     generalize (ecard s); intros H2.
     destruct H2.
     apply H3 in H0.
     apply t_lift_props.empty_is_empty_1 in H0; auto.
   Qed.


Lemma reductionhat_lift_monotone :
  forall chat_lift chat_lift',
    (order_lift chat_lift chat_lift') ->
    (order_lift (reductionhat_lift chat_lift) (reductionhat_lift chat_lift')).
  Proof.
   intros chat_lift chat_lift'.
   apply t_lift_props.set_induction with (s := chat_lift); intros.
   (* Base case: empty <= s *)
   unfold order_lift, reductionhat_lift; intros.
   apply t_lift_props.empty_is_empty_1 in H.
   unfold t_lift_union_fold in H1.
   rewrite  t_lift_props.fold_1b in H1.
   apply none_in_empty in H1; contradiction.
   apply t_lift_props.empty_is_empty_2 in H; assumption.
   (* Induction step *)
   (* We know that H2 means there exists a y in chat_lift' such that
      (abs.order x y) and that (order_lift s chat_lift') *)
   assert (exists y, t_lift.In y chat_lift' /\ (abs.order x y)) as subgoal.
     unfold order_lift in H2.
     generalize (H2 x); intros.
     assert (t_lift.In x s') as x_in_s'.
       generalize (H1 x); intros.
       apply H4.
       left; auto.
     apply H2 in x_in_s'.
     destruct x_in_s' as [y conj].
     destruct conj.
     exists y; auto.
  assert (order_lift s chat_lift') as subgoal2.
     unfold order_lift in H2.
     unfold order_lift; intros.
     generalize (H2 a0); intros help.
     unfold t_lift_props.Add in H1.
     generalize (H1 a0); intros a0_in_s'_def.
     assert (t_lift.In a0 s') as a0_in_s'.
       apply a0_in_s'_def; auto.
     apply help in a0_in_s'.
     assumption.
  apply H in subgoal2.
  unfold order_lift.
  intros a0 a0_in_redlift.
  case (t_dec.eq_dec a0 x).
    intro a0_eq_x.
    destruct subgoal as [y conj].
    destruct conj as [y_in_chat_lift' x_le_y].
    exists y.
    apply reductionhat_monotone in x_le_y.
    rewrite a0_eq_x.
  Qed.

 Lemma reductionhat_lift_sound :
  forall c chat_lift,
    (order_lift (alpha_lift c) chat_lift) ->
    (order_lift (alpha_lift (reduction c)) (reductionhat_lift chat_lift)).
  Proof.
  (* TODO *)
  Qed.

