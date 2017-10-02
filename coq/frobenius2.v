Definition lem := forall p, p \/ ~ p.
Print lem.

Definition frobenius := forall (A : Set) (p : A -> Prop) (q : Prop),
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).

Theorem lem_to_frobenius : lem -> frobenius.
Proof.
  firstorder.
Qed.

Theorem frobenius_to_lem: frobenius -> lem.
Proof.
  unfold lem, frobenius.
  firstorder.
  destruct (H {u : unit | p} (fun _ => False) p) as [G _].
  cut 
  apply G.
