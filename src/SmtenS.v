
Require Export Smten.
Require Export SmtenProp.
Require Export SmtenS1.

Module SmtenS.
Import Smten.Smten.
Import SmtenProp.SmtenProp.
Import SmtenS1.SmtenS1.

Inductive valueS : tm -> Prop :=
  | vS_return : forall t, valueS (treturnS t)
  | vS_zero : forall T, valueS (tzeroS T)
  .

Tactic Notation "valueS_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "vS_return" | Case_aux c "vS_zero" ].

Hint Constructors valueS.

Reserved Notation "t1 '=S=>' t2" (at level 40).

Inductive stepS : tm -> tm -> Prop :=
  | STS_STS1 : forall t t',
      t =S1=> t' ->
      t =S=> t'
  | STS_PlusLeft : forall t1 t2,
      tplusS (treturnS t1) t2 =S=> treturnS t1
  | STS_PlusRight : forall t1 t2,
      tplusS t1 (treturnS t2) =S=> treturnS t2
  | STS_PlusNotRight : forall T t,
      tplusS t (tzeroS T) =S=> t
  | STS_PlusNotLeft : forall T t,
      tplusS (tzeroS T) t =S=> t
  | STS_Plus1 : forall t1 t1' t2,
      t1 =S=> t1' ->
      tplusS t1 t2 =S=> tplusS t1' t2
  | STS_Plus2 : forall t1 t2 t2',
      t2 =S=> t2' ->
      tplusS t1 t2 =S=> tplusS t1 t2'

where "t1 '=S=>' t2" := (stepS t1 t2).

Tactic Notation "stepS_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STS_STS1"
  | Case_aux c "STS_PlusLeft" | Case_aux c "STS_PlusRight"
  | Case_aux c "STS_PlusNotRight" | Case_aux c "STS_PlusNotLeft"
  | Case_aux c "STS_Plus1" | Case_aux c "STS_Plus2" ].

Hint Constructors stepS.

Notation multistepS := (multi stepS).
Notation "t1 '=S=>*' t2" := (multistepS t1 t2) (at level 40).

Theorem progressS : forall t T,
    empty |- t \in T ->
    (exists T1 : ty, T = TS T1) ->
    valueS t \/ exists t', t =S=> t'.

Proof with eauto.
  intros t T Ht HSt.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var". inversion H.
  Case "T_Abs". inversion HSt. inversion H.
  Case "T_App". 
     (* progress says either tapp is a value or steps *)
     destruct (progress (tapp t1 t2) T12)...
     SCase "tapp is a value". inversion H.
     SCase "tapp steps". right. destruct H as [t3]...
  Case "T_Unit". inversion HSt. inversion H.
  Case "T_Pair". inversion HSt. inversion H.
  Case "T_Fst". 
     destruct(progress (tfst t) T1)...
     SCase "tfst is a value". inversion H.
     SCase "tfst steps". right. destruct H as [t2]...
  Case "T_Snd". 
     destruct (progress (tsnd t) T2)...
     SCase "tsnd is a value". inversion H.
     SCase "tsnd steps". right. destruct H as [t2]...
  Case "T_Inl". inversion HSt. inversion H.
  Case "T_Inr". inversion HSt. inversion H.
  Case "T_Case".
     destruct (progress (tcase t1 t2 t3) T3)...
     SCase "tcase is a value". inversion H.
     SCase "tcase steps". right. destruct H as [t4]...
  Case "T_ReturnIO". inversion HSt. inversion H.
  Case "T_BindIO". inversion HSt. inversion H.
  Case "T_SearchIO". inversion HSt. inversion H.
  Case "T_BindS".
     right. destruct (progressS1 t1 (TS T1))...
     SCase "t1 is a valueS1".
       inversion H.
       SSCase "t1 is returnS".
         exists (tapp t2 t). apply STS_STS1. apply STS1_BindReturn.
       SSCase "t1 is zeroS".
         exists (tzeroS T2). apply STS_STS1. apply STS1_BindZero.
         rewrite <- H0 in Ht1. inversion Ht1...
       SSCase "t1 is plusS".
         exists (tplusS (tbindS t0 t2) (tbindS t3 t2)).
         apply STS_STS1. apply STS1_BindPlus.
     SCase "t1 steps".
       inversion H as [t1'].
       exists (tbindS t1' t2).
       apply STS_STS1. apply STS1_Bind. assumption.
  Case "T_PlusS".
     right. destruct IHHt1...
     SCase "t1 is a valueS".
       inversion H.
       SSCase "t1 is returnS".
          exists (treturnS t). apply STS_PlusLeft.
       SSCase "t1 is zeroS".
          exists t2. apply STS_PlusNotLeft.
     SCase "t1 steps".
       inversion H as [t1'].
       exists (tplusS t1' t2).
       apply STS_Plus1...
Qed.

Theorem preservationS : forall t t' T,
     empty |- t \in T ->
     t =S=> t' ->
     empty |- t' \in T.

Proof with eauto.
   intros t t' T HT Hstep.
   generalize dependent T.
   stepS_cases (induction Hstep) Case; intros Tx HT; subst...
   Case "STS_STS1". apply preservationS1 with t...
   Case "STS_PlusLeft". inversion HT...
   Case "STS_PlusRight". inversion HT...
   Case "STS_PlusNotRight". inversion HT...
   Case "STS_PlusNotLeft". inversion HT...
   Case "STS_Plus1". inversion HT...
   Case "STS_Plus2". inversion HT...
Qed.

Theorem preservationS_multi : forall t t' T,
  empty |- t \in T ->
  t =S=>* t' ->
  empty |- t' \in T
  .
Proof.
  intros t t' T HT Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". assumption.
  Case "multi_step". 
     apply IHHsteps.
     apply preservationS with x0. assumption. assumption.
Qed.

Definition stuckS (t:tm) : Prop :=
  (normal_form stepS) t /\ ~ valueS t.

Corollary soundnessS : forall t t' T,
  empty |- t \in T -> 
  (exists T1, T = TS T1) ->
  t =S=>* t' ->
  ~(stuckS t').
Proof.
  intros t t' T Hhas_type Hio Hmulti. unfold stuckS.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti. apply Hnot_val. 
   destruct (progressS x0 T).
   apply Hhas_type. apply Hio. apply H.
   contradiction.

   apply IHHmulti.
   apply (preservationS x0 y0). apply Hhas_type. apply H.
   apply Hnf. apply Hnot_val.
Qed.

Inductive unsat : tm -> Prop :=
  | Un_Zero : forall T, unsat (tzeroS T)
  | Un_Step : forall t T,
      empty |- t \in TS T ->
      (exists t', t =S=> t') ->
      (forall t', t =S=> t' -> unsat t') ->
      unsat t
  .

Tactic Notation "unsat_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Un_Zero" | Case_aux c "Un_Step" ].

Hint Constructors unsat.

Theorem unsat_goes_zero : forall t T,
  empty |- t \in TS T ->
  unsat t ->
  t =S=>* tzeroS T
  .
Proof.
  intros t T HT Hunsat.
  unsat_cases (induction Hunsat) Case.
  Case "Un_Zero".
    inversion HT.
    apply multi_refl.
  Case "Un_Step".
    destruct (progressS t (TS T)). assumption.
    exists T. reflexivity.
    SCase "t is a valueS".
      valueS_cases (inversion H3) SSCase.
      SSCase "vS_return".
        inversion H0.
        rewrite <- H4 in H5.
        inversion H5. inversion H6. inversion H9.      
      SSCase "vS_zero".
        rewrite <- H4 in HT.
        inversion HT.
        apply multi_refl.
    SCase "t steps".
      inversion H3 as [t1].
      apply multi_step with t1. assumption.
      apply H2. assumption. apply preservationS with t.
      assumption. assumption.
Qed.

Theorem unsat_preserves : forall t t' T,
  empty |- t \in TS T ->
  unsat t ->
  t =S=> t' ->
  unsat t'
  .
Proof.
  intros t t' T HT Hunsat Hstep.
  unsat_cases (inversion Hunsat) Case.
  Case "Un_Zero".
    rewrite <- H in Hstep.
    inversion Hstep.
    inversion H0.
    inversion H3.
  Case "Un_Step".
    apply H1.
    assumption.
Qed.

Theorem unsat_preserves_multi : forall t t' T,
  empty |- t \in TS T ->
  unsat t ->
  t =S=>* t' ->
  unsat t'
  .
Proof.
  intros t t' T HT Hunsat Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". assumption.
  Case "multi_step". 
     apply IHHsteps.
     apply preservationS with x0. assumption. assumption.
     apply unsat_preserves with x0 T. assumption. assumption.
     assumption.
Qed.

Theorem unsat_goes_only_zero : forall t tv T,
  empty |- t \in TS T ->
  unsat t ->
  t =S=>* tv ->
  valueS tv ->
  tv = tzeroS T
  .
Proof.
  intros t tv T HT Hunsat Hsteps Hval.
  assert (unsat tv).
  apply unsat_preserves_multi with t T.
  assumption. assumption. assumption.
  valueS_cases (destruct Hval) Case.
  Case "vS_return".
    inversion H.
    inversion H1. inversion H4. inversion H5. inversion H8.
  Case "vS_zero".
    f_equal.
    assert (empty |- tzeroS T0 \in TS T).
    apply preservationS_multi with t.
    assumption. assumption.
    inversion H0. reflexivity.
Qed.

Theorem unsat_plus_unsat_zero : forall t T,
  empty |- t \in TS T ->
  unsat t ->
  unsat (tplusS t (tzeroS T))
  .
Proof.
  intros t T HT Hunsat.
  unsat_cases (induction Hunsat) Case.
  Case "Un_Zero".
    apply Un_Step with T.
    apply T_PlusS. assumption. apply T_ZeroS.
    exists (tzeroS T). apply STS_PlusNotLeft.
    intros tv Hstep.
    inversion Hstep.
    SCase "Pure". inversion H. inversion H2.
    SCase "PlusNotRight". apply Un_Zero.
    SCase "PlusNotLeft". apply Un_Zero.
    SCase "Plus1". inversion H2. inversion H3. inversion H6.
    SCase "plus2". inversion H2. inversion H3. inversion H6.
  Case "Un_Step".
    apply Un_Step with T.
    apply T_PlusS. assumption. apply T_ZeroS.
    exists t. apply STS_PlusNotRight.
    intros tv Hstep.
    inversion Hstep.
    SCase "Pure". inversion H3. inversion H6.
    SCase "PlusLeft".
      inversion H0.
      rewrite <- H4 in H6. inversion H6. inversion H7. inversion H10.
    SCase "PlusNotRight".
      rewrite <- H3.
      apply Un_Step with T.
      assumption. assumption. assumption.
    SCase "PlusNotLeft". apply Un_Zero.
    SCase "Plus1".
      apply H2. assumption. 
      apply preservationS with t. assumption. assumption.
    SCase "Plus2". inversion H6. inversion H7. inversion H10.
Qed.

Theorem unsat_plus_if : forall t1 t2 T,
  empty |- t1 \in TS T ->
  empty |- t2 \in TS T ->
  unsat t1 ->
  unsat t2 ->
  unsat (tplusS t1 t2)
  .
Proof.
  intros t1 t2 T HT1  HT2 Hunsat1 Hunsat2.
  generalize dependent t2.
  unsat_cases (induction Hunsat1) Case; intros t2 HT2 Hunsat2.
  Case "Un_Zero".
    unsat_cases (induction Hunsat2) SCase.
    SCase "Un_Zero".
      apply unsat_plus_unsat_zero.
      inversion HT1.
      inversion HT2.
      apply T_ZeroS.
      apply Un_Zero.
    SCase "Un_Step".
      apply Un_Step with T.
      apply T_PlusS. assumption. assumption.
      exists t. apply STS_PlusNotLeft.
      intros tv Hstep.
      inversion Hstep.
      SSCase "Pure". inversion H3. inversion H6.
      SSCase "PlusLeft".
        inversion H0.
        rewrite <- H5 in H6. inversion H6. inversion H7. inversion H10.
      SSCase "PlusNotRight". apply Un_Zero.
      SSCase "PlusNotLeft".
        rewrite <- H3.
        apply Un_Step with T.
        assumption. assumption. assumption.
      SSCase "Plus1". inversion H6. inversion H7. inversion H10.
      SSCase "Plus2".
        apply H2. assumption. 
        apply preservationS with t. assumption. assumption.
   Case "Un_Step".
     unsat_cases (induction Hunsat2) SCase.
     SCase "Un_Zero".
       apply unsat_plus_unsat_zero.
       inversion HT2. assumption.
       apply Un_Step with T. assumption. assumption. assumption.
     SCase "Un_Step".
       apply Un_Step with T.
       apply T_PlusS. assumption. assumption.
       inversion H0 as [t2].
       exists (tplusS t2 t0). apply STS_Plus1. assumption.
       intros tv Hstep.
       inversion Hstep.
       SSCase "Pure". inversion H7. inversion H10.
       SSCase "PlusLeft". 
         rewrite <- H8 in H0.
         inversion H0.
         inversion H10. inversion H11. inversion H14.
       SSCase "PlusRight".
         rewrite <- H9 in H4.
         inversion H4. inversion H10. inversion H11. inversion H14.
       SSCase "PlusNotRight".
         rewrite <- H7.
         apply Un_Step with T.
         assumption. assumption. assumption.
       SSCase "PlusNotLeft".
         rewrite <- H7.
         apply Un_Step with T; assumption.
       SSCase "Plus1".
         apply H2. assumption.
         apply preservationS with t. assumption. assumption. assumption.
         apply Un_Step with T; assumption.
       SSCase "Plus2".
         apply H6. assumption.
         apply preservationS with t0; assumption.
Qed.

Theorem unsat_plus_only : forall t t1 t2 T,
  empty |- t \in TS T ->
  unsat t ->
  t = tplusS t1 t2 ->
  unsat t1 /\ unsat t2
  .
Proof.
  intros t t1 t2 T HT Hunsat Hdef.
  generalize dependent t2.
  generalize dependent t1.
  unsat_cases (induction Hunsat) Case; intros t1 t2 Hdef.
  Case "Un_Zero". inversion Hdef.
  Case "Un_Step".
    rewrite Hdef in *. clear Hdef.
    split.
    destruct (progressS t1) with (TS T).
    inversion HT. assumption. exists T. reflexivity.
    SCase "valueS t1".
      valueS_cases (destruct H3) SSCase.
      SSCase "vS_return".
        apply H1.
        apply STS_PlusLeft.
      SSCase "vS_zero".
        apply Un_Zero.
    SCase "t1 steps".
      apply Un_Step with T.
      inversion HT. assumption.
      assumption.
      intros tv Hstep.

      assert (Hpstep : tplusS t1 t2 =S=> tplusS tv t2).
      apply STS_Plus1. assumption.

      assert (HpT : empty |- (tplusS tv t2) \in TS T).
      inversion HT.
      apply T_PlusS.
      apply preservationS with t1.
      assumption. assumption. assumption.

      assert (Hpeq : tplusS tv t2 = tplusS tv t2).
      reflexivity.

      specialize (H2 (tplusS tv t2) Hpstep HpT tv t2 Hpeq).
      decompose [and] H2.
      assumption.
     
    destruct (progressS t2) with (TS T).
    inversion HT. assumption. exists T. reflexivity.
    SCase "valueS t2".
      valueS_cases (destruct H3) SSCase.
      SSCase "vS_return".
        apply H1.
        apply STS_PlusRight.
      SSCase "vS_zero".
        apply Un_Zero.
    SCase "t2 steps".
      apply Un_Step with T.
      inversion HT. assumption.
      assumption.
      intros tv Hstep.

      assert (Hpstep : tplusS t1 t2 =S=> tplusS t1 tv).
      apply STS_Plus2. assumption.

      assert (HpT : empty |- (tplusS t1 tv) \in TS T).
      inversion HT.
      apply T_PlusS.
      assumption.
      apply preservationS with t2.
      assumption. assumption.

      assert (Hpeq : tplusS t1 tv = tplusS t1 tv).
      reflexivity.

      specialize (H2 (tplusS t1 tv) Hpstep HpT t1 tv Hpeq).
      decompose [and] H2.
      assumption.
Qed.

Theorem plus1_multi : forall t1 t1' t2 T,
  empty |- t1 \in TS T ->
  empty |- t2 \in TS T ->
  t1 =S=>* t1' ->
  tplusS t1 t2 =S=>* tplusS t1' t2
  .
Proof.    
  intros t1 t1' t2 T HT1 HT2 Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". apply multi_refl.
  Case "multi_step". 
    apply multi_step with (tplusS y0 t2).
    apply STS_Plus1. assumption.
    apply IHHsteps.
    apply preservationS with x0; assumption.
Qed.

Theorem plus2_multi : forall t1 t2 t2' T,
  empty |- t1 \in TS T ->
  empty |- t2 \in TS T ->
  t2 =S=>* t2' ->
  tplusS t1 t2 =S=>* tplusS t1 t2'
  .
Proof.    
  intros t1 t2 t2' T HT1 HT2 Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". apply multi_refl.
  Case "multi_step". 
    apply multi_step with (tplusS t1 y0).
    apply STS_Plus2. assumption.
    apply IHHsteps.
    apply preservationS with x0; assumption.
Qed.
 
 
Theorem unsat_expands : forall t t' T,
  empty |- t \in TS T ->
  unsat t' ->
  t =S=> t' ->
  unsat t
  .


Ltac sts1_det t t' T :=
   inversion Hstep; apply Un_Step with T;
   [ assumption
   | exists t'; assumption
   | intros tv Hstep1; assert (Heq : tv = t');
     [ inversion Hstep1; apply stepS1_deterministic with t (TS T); assumption
     | rewrite Heq; assumption ]].

   
Proof.
  intro t.
  t_cases (induction t) Case; intros t' T HT Hunsat Hstep.
  Case "tvar". sts1_det (tvar i) t' T.
  Case "tapp". sts1_det (tapp t1 t2) t' T.
  Case "tabs". sts1_det (tabs i t t0) t' T.
  Case "tunit". sts1_det tunit t' T.
  Case "tpair". sts1_det (tpair t1 t2) t' T.
  Case "tfst". sts1_det (tfst t) t' T.
  Case "tsnd". sts1_det (tsnd t) t' T.
  Case "tinl". sts1_det (tinl t t0) t' T.
  Case "tinr". sts1_det (tinr t t0) t' T.
  Case "tcase". sts1_det (tcase t1 t2 t3) t' T.
  Case "tfix". sts1_det (tfix t) t' T.
  Case "treturnIO". sts1_det (treturnIO t) t' T.
  Case "tbindIO". sts1_det (tbindIO t1 t2) t' T.
  Case "tsearchIO". sts1_det (tsearchIO t) t' T.
  Case "treturnS". sts1_det (treturnS t) t' T.
  Case "tbindS". sts1_det (tbindS t1 t2) t' T.
  Case "tzeroS". sts1_det (tzeroS t) t' T.
  Case "tplusS".
    inversion Hstep.
    SCase "S1". inversion H. inversion H2.
    SCase "PlusLeft". (* but treturn is not unsat *)
      rewrite <- H2 in Hunsat.
      inversion Hunsat.
      inversion H3. inversion H6. inversion H7. inversion H10.
    SCase "PlusRight". (* but treturn is not unsat *)
      rewrite <- H2 in Hunsat.
      inversion Hunsat.
      inversion H3. inversion H6. inversion H7. inversion H10.
    SCase "PlusNotRight".
      apply unsat_plus_if with T.
      apply preservationS with (tplusS t1 t2) . assumption. assumption.
      rewrite H1. inversion HT. assumption. assumption.
      apply Un_Zero.
    SCase "PlusNotLeft".
      apply unsat_plus_if with T.
      rewrite H0.
      inversion HT. assumption.
      apply preservationS with (tplusS t1 t2). assumption. assumption.
      apply Un_Zero. assumption.
    SCase "Plus1".
      rewrite <- H0 in Hunsat.
      inversion HT.
      assert (empty |- t1' \in TS T).
      apply preservationS with t1; assumption.
    
      assert (unsat t1').
      apply proj1 with (unsat t2).
      apply unsat_plus_only with (tplusS t1' t2) T.
      apply T_PlusS ; assumption.
      assumption. reflexivity.

      assert (unsat t1).
      apply IHt1 with t1' T; assumption.
 
      assert (tplusS t1' t2 =S=>* tplusS (tzeroS T) t2).
      apply plus1_multi with T ;
      [ assumption | assumption | apply unsat_goes_zero ; assumption ].
      
      assert (unsat (tplusS (tzeroS T) t2)).
      apply unsat_preserves_multi with (tplusS t1' t2) T.
      apply T_PlusS; assumption. assumption. assumption.

      assert (unsat t2).
      apply unsat_preserves with (tplusS (tzeroS T) t2) T.
      apply T_PlusS . apply T_ZeroS. assumption.
      assumption.
      apply STS_PlusNotLeft.
      
      apply unsat_plus_if with T; assumption.

    SCase "Plus2".
      rewrite <- H0 in Hunsat.
      inversion HT.
      assert (empty |- t2' \in TS T).
      apply preservationS with t2; assumption.
    
      assert (unsat t2').
      apply proj2 with (unsat t1).
      apply unsat_plus_only with (tplusS t1 t2') T.
      apply T_PlusS ; assumption.
      assumption. reflexivity.

      assert (unsat t2).
      apply IHt2 with t2' T; assumption.
 
      assert (tplusS t1 t2' =S=>* tplusS t1 (tzeroS T)).
      apply plus2_multi with T ;
      [ assumption | assumption | apply unsat_goes_zero ; assumption ].
      
      assert (unsat (tplusS t1 (tzeroS T))).
      apply unsat_preserves_multi with (tplusS t1 t2') T.
      apply T_PlusS; assumption. assumption. assumption.

      assert (unsat t1).
      apply unsat_preserves with (tplusS t1 (tzeroS T)) T.
      apply T_PlusS . assumption. apply T_ZeroS.
      assumption.
      apply STS_PlusNotRight.
      
      apply unsat_plus_if with T; assumption.
Qed.

Theorem unsat_expands_multi : forall t t' T,
  empty |- t \in TS T ->
  unsat t' ->
  t =S=>* t' ->
  unsat t
  .
Proof.
  intros t t' T HT Hunsat Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". assumption.
  Case "multi_step". 
     apply unsat_expands with y0 T. assumption.
     apply IHHsteps.
     apply preservationS with x0 ; assumption.
     assumption. assumption.
Qed.

Theorem perseverence : forall t1 t2 T,
   empty |- t1 \in TS T ->
   t1 =S=>* tzeroS T ->
   t1 =S=>* t2 ->
   valueS t2 ->
   t2 = tzeroS T
  .
Proof.
   intros t1 t2 T HT Htozero Htot2 Hvt2.
   apply unsat_goes_only_zero with t1.
   assumption.
   apply unsat_expands_multi with (tzeroS T) T.
   assumption.
   apply Un_Zero. assumption. assumption. assumption.
Qed.   
  
End SmtenS.

