Inductive Nat : Type :=
  z : Nat
| s : Nat -> Nat
.
Eval simpl in nat_ind.
Eval simpl in Nat_ind.

Eval simpl in z.
Eval simpl in s(s z).


Fixpoint add(l:Nat)(r:Nat) : Nat :=
  match l with
  | z => r
  | s l' => s (add l' r)
end.

Eval simpl in add (s z) (s (s z)).

Lemma add_succ : forall l r : Nat, s (add l r) = add l (s r).
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.

Theorem add_comm : forall l r : Nat, add l r = add r l.
Proof.
  intros.
  induction l.
  simpl.
  induction r.
  reflexivity.
  simpl.
  rewrite <- IHr.
  reflexivity.
  simpl.
  rewrite IHl.
  assert (forall x y, s(add x y) = add x (s y)).
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite <- IHx.
  reflexivity.
  apply H.
Qed.
  
Fixpoint add_tr(l:Nat)(r:Nat) : Nat :=
  match l with
  | z => r
  | s l' => add_tr l' (s r)
end.

Eval simpl in add_tr (s z) (s (s z)).

Lemma add_tailrec_succ : forall l r : Nat, add_tr (s l) r = add_tr l (s r).
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem add_tailrec_comm : forall l r : Nat, add_tr l r = add_tr r l.
Proof.
  intros.
  induction l.
  simpl.
  assert (forall x, add_tr z x = add_tr x z).
  induction x.
  reflexivity.
  simpl.
  assert (forall x, add_tr x (s z) = s (add_tr x z)).
  induction x0.
  simpl.
  reflexivity.
  
