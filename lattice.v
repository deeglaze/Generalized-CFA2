Require Import Ensembles.
Require Import Partial_Order.

Section Identities.
 Variable L : Type.
 Variable binop : L -> L -> L.
 Record idents : Type := Definition_of_Identities
  { Id_symmetric : forall a b, (binop a b) = (binop b a);
    Id_associative : forall a b c, (binop (binop a b) c) = (binop a (binop b c));
    Id_idempotent : forall a, (binop a a) = a }.
End Identities.

Section Bounds.
 Variable L : Type.
 Variable L_partially_ordered : (PO L).
 Definition le := Rel_of L L_partially_ordered.
 Definition upper_bound c a b := (le a c) /\ (le b c).
 Definition lower_bound c a b := (le c a) /\ (le c b).
End Bounds.

Module Type MeetSemiLattice.
 Parameter L : Type.
 Parameter L_partially_ordered : (PO L).

 Definition le := Rel_of L L_partially_ordered.
 Definition LB := lower_bound L L_partially_ordered.

 Parameter meet : L -> L -> L.
 Axiom meet_is_lb : forall a b : L, LB (meet a b) a b.
 Axiom meet_is_glb : forall a b lb : L, LB lb a b -> le lb (meet a b).
 Axiom meet_idents : idents L meet.
End MeetSemiLattice.

Module Type JoinSemiLattice.
 Parameter L : Type.
 Parameter L_partially_ordered : (PO L).

 Definition le := Rel_of L L_partially_ordered.
 Definition UB := upper_bound L L_partially_ordered.

 Parameter join : L -> L -> L.
 Axiom join_is_lb : forall a b : L, UB (join a b) a b.
 Axiom join_is_lub : forall a b ub : L, UB ub a b -> le (join a b) ub.
 Axiom join_idents : idents L join.
End JoinSemiLattice.

Module Type MeetSemiLatticeWithBottom (Import msl : MeetSemiLattice).
 Parameter bot : L.
 Axiom bot_is_bottom : forall a : L, le bot a.
 Axiom meet_bottom : forall a : L, (meet a bot) = bot.
End MeetSemiLatticeWithBottom.

Module Type JoinSemiLatticeWithTop (Import jsl : JoinSemiLattice).
 Parameter top : L.
 Axiom top_is_top : forall a : L, le a top.
 Axiom join_top : forall a : L, (join a top) = top.
End JoinSemiLatticeWithTop.

Module Type Lattice (Import jsl : JoinSemiLattice)
                    (Import msl : MeetSemiLattice).
End Lattice.

Print Module Type JoinSemiLatticeWithTop.

Module Type CompleteLattice (Import jsl : JoinSemiLattice) (Import msl : MeetSemiLattice).
 Print jsl.
 Print JoinSemiLatticeWithTop.
 Parameter top : L.
 Axiom top_is_top : forall a : L, le a top.
 Axiom join_top : forall a : L, (join a top) = top.
 Module Type JSLT := (JoinSemiLatticeWithTop with Module jsl := jsl).
End CompleteLattice.