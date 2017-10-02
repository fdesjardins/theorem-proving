Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).

Proof.
  firstorder.
Qed.
