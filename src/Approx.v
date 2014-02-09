
Module Approx.

Definition unsat {T: Type} (x : T -> Prop) : Prop
    := forall t, ~(x(t))
    .

Definition approx {T: Type} (a : T -> Prop) (b : T -> Prop) (x : T -> Prop) : Prop
    := (forall t, a(t) -> x(t))
    /\ (forall t, x(t) -> b(t))
    .

Theorem approx_useful_sat : forall T xi xo xx m,
    @approx T xi xo xx ->
    xi(m) ->
    xx(m)
    .
Proof.
  intros T xi xo xx m Happrox Hsat.
  unfold approx in Happrox.
  decompose [and] Happrox.
  apply H ; assumption.
Qed.

Theorem approx_useful_unsat : forall T xi xo xx,
    @approx T xi xo xx ->
    unsat xo ->
    unsat xx
    .
Proof.
  intros T xi xo xx Happrox Hunsat.
  unfold unsat.
  intros t Hxx.
  unfold approx in Happrox.
  unfold unsat in Hunsat.
  apply (Hunsat t).
  decompose [and] Happrox.
  apply H0 ; assumption.
Qed.


(* An approximation for something known completely *)
Theorem approx_known : forall T x,
    @approx T x x x
    .
Proof.
  intros T x.
  unfold approx.
  split ; intros ; assumption.
Qed.

(* An approximation for something completely unknown *)
Theorem approx_unknown : forall T x,
    @approx T (fun _ => False) (fun _ => True) x
    .
Proof.
  intros T x.
  unfold approx.
  split.
   contradiction.
   split.
Qed.

Theorem approx_not : forall T xi xo x,
    approx xi xo x ->
    @approx T (fun m => ~xo(m)) (fun m => ~xi(m)) (fun m => ~x(m))
    .
Proof.
  intros T xi xo x Happrox.
  unfold approx in *.
  decompose [and] Happrox.
  unfold not in *.
  split.
   intros t Ho Hxt. apply Ho. apply H0. apply Hxt.
   intros t Hxt Hi. apply Hxt. apply H. apply Hi.
Qed.   

Theorem approx_and : forall T xi xo xx yi yo yy,
    approx xi xo xx ->
    approx yi yo yy ->
    @approx T (fun m => xi(m) /\ yi(m)) (fun m => xo(m) /\ yo(m)) (fun m => xx(m) /\ yy(m))
    .
Proof.
  intros T xi xo xx yi yo yy Happx Happy.
  unfold approx in *.
  split.
   intros t His. split.
    apply Happx. apply His.
    apply Happy. apply His.
   intros t Hxy. split.
    apply Happx. apply Hxy.
    apply Happy. apply Hxy.
Qed.

(* Approximation of if then else *)
Theorem approx_ite : forall T pi po p xi xo x yi yo y,
    approx pi po p ->
    approx xi xo x ->
    approx yi yo y ->
    @approx T (fun m => (pi(m) /\ xi(m)) \/ (~po(m) /\ yi(m)))
              (fun m => (po(m) /\ xo(m)) \/ (~pi(m) /\ yo(m)))
              (fun m => (p(m) /\ x(m)) \/ (~p(m) /\ y(m)))
    .
Proof.
  intros T pi po p xi xo x yi yo y Hp Hx Hy.
  unfold approx in *.
  split.
   intros Ht H. elim H.
    intro Hh. left. split.
     apply Hp. apply Hh.
     apply Hx. apply Hh.
    intro Hh. right. split.
     intro Hptrue. absurd (po Ht).
      apply Hh.
      apply Hp. assumption.
     apply Hy. apply Hh.
   intros t H. elim H.
    intro Hh. left. split.
     apply Hp ; apply Hh.
     apply Hx ; apply Hh.
    intro Hh. right. split.
     intro Hpitrue. absurd (p t).
      apply Hh.
      apply Hp. assumption.
     apply Hy ; apply Hh.
Qed.

End Approx.

