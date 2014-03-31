
Section Approx2.

Variable Model : Type.

Definition BoolF : Type := Model -> bool.

Definition unsat (x : BoolF) : Prop :=
    forall m, ~ eq_true (x m)
    .

(* We approximate an element as:
    p - condition under which the element is known.
    a - value of the element when known.
    b - value of the element when unknown.
*)
Definition approx (T : Type) (x : Model -> T) (p : BoolF) (a : Model -> T) (b : Model -> T) : Prop
    := (forall t, x t = if p t then a t else b t)
    .

Theorem approx_useful_sat : forall x xp xa xb m,
    approx x xp xa xb ->
    eq_true (andb (xp m) (xa m)) ->
    eq_true (x m)
    .

Theorem approx_useful_unsat : forall x xp xa xb,
    approx x xp xa xb ->
    unsat

Lemma i_implies_o : forall xi xo xx,
    approx xi xo xx ->
    forall m, eq_true (xi m) -> eq_true (xo m)
    .
Proof.
  intros xi xo xx Ha m Hxi.
  unfold approx in Ha.
  decompose [and] Ha.
  specialize H with m.
  specialize H0 with m.
  exact (H0 (H Hxi)).
Qed.

(* An approximation for something known completely *)
Theorem approx_known : forall x,
    approx x x x
    .
Proof.
  intros x.
  unfold approx.
  split ; intros ; assumption.
Qed.

(* An approximation for something completely unknown *)
Theorem approx_unknown : forall x,
    approx (fun _ => false) (fun _ => true) x
    .
Proof.
  intros x.
  unfold approx.
  split.
   intros m Habsurd. inversion Habsurd.
   split.
Qed.

Theorem approx_not : forall xi xo x,
    approx xi xo x ->
    approx (fun m => negb (xo m)) (fun m => negb (xi m)) (fun m => negb (x m))
    .
Proof.
  intros xi xo x Happrox.
  unfold approx in *.
  decompose [and] Happrox.
  unfold not in *.
  split.
   intros m Ho. specialize H0 with m. destruct (x m).
    set (Hno := H0 is_eq_true). destruct (xo m) ; assumption.
    simpl. exact is_eq_true.

   intros m Hx. specialize H with m. destruct (xi m).
    set (Hnx := H is_eq_true). destruct (x m) ; assumption.
    exact is_eq_true.
Qed.

Theorem approx_and : forall xi xo xx yi yo yy,
    approx xi xo xx ->
    approx yi yo yy ->
    approx (fun m => andb (xi m) (yi m)) (fun m => andb (xo m) (yo m)) (fun m => andb (xx m) (yy m))
    .
Proof.
  intros xi xo xx yi yo yy Hax Hay.
  unfold approx in *.
  split.
   intros m His.
    decompose [and] Hax.
    specialize H with m.
    decompose [and] Hay.
    specialize H1 with m.
    destruct (xx m).
    destruct (yy m).
     exact (is_eq_true).
     destruct (yi m).
     exact (H1 is_eq_true).
     destruct (xi m).
     simpl in His. elim His. exact is_eq_true.
     simpl in His. elim His. exact is_eq_true.
    simpl.
    destruct (xi m).
     exact (H is_eq_true).
     apply His.
  
   intros m Hxy.
   decompose [and] Hax.
   specialize H0 with m.
   decompose [and] Hay.
   specialize H2 with m.
   destruct (xo m).
    destruct (yo m).
     exact (is_eq_true).
     apply H2. destruct (yy m).
      exact is_eq_true.
      destruct (xx m) ; apply Hxy.
    destruct (xx m).
     exact (H0 is_eq_true).
     apply Hxy.
Qed.

(* Approximation of if then else *)
Theorem approx_ite : forall pi po p xi xo x yi yo y,
    approx pi po p ->
    approx xi xo x ->
    approx yi yo y ->
    approx (fun m => orb (andb (pi m) (xi m)) (andb (negb (po m)) (yi m)))
           (fun m => orb (andb (po m) (xo m)) (andb (negb (pi m)) (yo m)))
           (fun m => if p m then x m else y m)
    .
Proof.
  intros pi po p xi xo x yi yo y Hap Hax Hay.
  unfold approx in *.
  split.
   intros m Htr.
   decompose [and] Hap.
   decompose [and] Hax.
   decompose [and] Hay.
   specialize H with m.
   specialize H0 with m.
   specialize H1 with m.
   specialize H3 with m.
   destruct (pi m), (po m), (p m), (xi m), (xo m), (x m), (yi m), (yo m), (y m) ; auto.
 
   intros m Htr.
   decompose [and] Hap.
   decompose [and] Hax.
   decompose [and] Hay.
   specialize H with m.
   specialize H0 with m.
   specialize H2 with m.
   specialize H4 with m.
   destruct (pi m), (po m), (p m), (xi m), (xo m), (x m), (yi m), (yo m), (y m) ; auto.
Qed.

Variable Elem : Type.
Definition ElemF : Type := Model -> Elem.


(* We approximate an assignment-parameterized element x using:
    p - a predicate determining when the approximation is exact
    a - the approximation.
*)
Definition eapprox (p : BoolF) (a : ElemF) (x : ElemF) : Prop
    := forall m, eq_true (p m) -> a(m) = x(m)
    .

Theorem eapprox_known : forall x,
    eapprox (fun _ => true) x x
    .
Proof.
  intros x m Hp. reflexivity.
Qed.

Theorem eapprox_unknown : forall x bot,
    eapprox (fun _ => false) bot x
    .
Proof.
  intros x bot m Hp.
  inversion Hp.
Qed.

Theorem approx_unary : forall f xp xa xx,
    eapprox xp xa xx ->
    approx (fun m => andb (xp m) (f (xa m)))
           (fun m => orb (negb (xp m)) (f (xa m)))
           (fun m => f (xx m))
    .
  intros f xp xa xx Hax.
  split.
  unfold eapprox in Hax.
  intro m.
  specialize Hax with m.
  destruct (xp m).
   simpl.
   rewrite (Hax is_eq_true).
   trivial.
   
   simpl.
   intro Hsilly.
   inversion Hsilly.

  intros m Htr.
  unfold eapprox in Hax.
  specialize Hax with m.
  destruct (xp m).
   rewrite (Hax is_eq_true).
   trivial.
 
   exact (is_eq_true).
Qed.
  
  
Theorem approx_binary : forall f xp xa xx yp ya yy,
    eapprox xp xa xx ->
    eapprox yp ya yy ->
    approx (fun m => andb (xp m) (andb (yp m) (f (xa m) (ya m))))
           (fun m => orb (negb (xp m)) (orb (negb (yp m)) (f (xa m) (ya m))))
           (fun m => f (xx m) (yy m))
    .
Proof.
  intros f xp xa xx yp ya yy Hax Hay.
  split ; intros m H; unfold eapprox in *;
          specialize Hax with m; specialize Hay with m ;
          destruct (xp m), (yp m) ; simpl in H.
    rewrite <- (Hax is_eq_true).
    rewrite <- (Hay is_eq_true).
    assumption.

    inversion H.
    inversion H.
    inversion H.

    rewrite (Hax is_eq_true).
    rewrite (Hay is_eq_true).
    assumption.

    exact (is_eq_true).
    exact (is_eq_true).
    exact (is_eq_true).
Qed.

Theorem eapprox_unary : forall f xp xa xx,
    eapprox xp xa xx ->
    eapprox xp (fun m => f (xa m)) (fun m => f (xx m))
    .
Proof.
  intros f xp xa xx Hax.
  unfold eapprox in *.
  intros m Heq.
  specialize Hax with m.
  rewrite (Hax Heq).
  reflexivity.
Qed.  

Theorem eapprox_binary : forall f xp xa xx yp ya yy,
    eapprox xp xa xx ->
    eapprox yp ya yy ->
    eapprox (fun m => andb (xp m) (yp m)) (fun m => f (xa m) (ya m)) (fun m => f (xx m) (yy m))
    .
Proof.
  intros f xp xa xx yp ya yy Hax Hay.
  unfold eapprox in *.
  intros m Heq.
  specialize Hax with m.
  specialize Hay with m.
  destruct (xp m), (yp m).
  rewrite (Hax is_eq_true).
  rewrite (Hay is_eq_true).
  reflexivity.
  inversion Heq.
  inversion Heq.
  inversion Heq.
Qed.

Theorem eapprox_ite : forall pi po pp xp xa xx yp ya yy,
    approx pi po pp ->
    eapprox xp xa xx ->
    eapprox yp ya yy ->
    eapprox (fun m => orb (andb (pi m) (xp m)) (andb (negb (po m)) (yp m)))
            (fun m => if pi m then xa m else ya m)
            (fun m => if pp m then xx m else yy m)
    .
Proof.
  intros pi po pp xp xa xx yp ya yy Hap Hax Hay m H.
  unfold approx in Hap.
  decompose [and] Hap.
  unfold eapprox in *.
  specialize H0 with m.
  specialize H1 with m.
  specialize Hax with m.
  specialize Hay with m.
  destruct (pi m), (pp m), (xp m).
  rewrite (Hax is_eq_true) ; reflexivity.
  destruct (po m).
  inversion H.
  rewrite (Hax (H1 is_eq_true)) ; reflexivity.
  set (Hsilly := H0 is_eq_true).
  inversion Hsilly.
  set (Hsilly := H0 is_eq_true) ; inversion Hsilly.
  destruct (po m).
  inversion H.
  set (Hsilly := H1 is_eq_true) ; inversion Hsilly.
  destruct (po m).
  inversion H.
  set (Hsilly := H1 is_eq_true) ; inversion Hsilly.
  destruct (yp m).
  exact (Hay is_eq_true).
  destruct (po m) ; inversion H.
  destruct (yp m).
  exact (Hay is_eq_true).
  destruct (po m) ; inversion H.
Qed. 

End Approx2.
