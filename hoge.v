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

Fixpoint add_tr(l:Nat)(r:Nat) : Nat :=
  match l with
  | z => r
  | s l' => add l' (s r)
end.

Lemma add_tailrec_succ : forall l r : Nat, s (add_tr l r) = add_tr l (s r).
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.
