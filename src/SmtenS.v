
Require Export Smten.
Require Export SmtenProp.
Require Export SmtenS1.

Module SmtenS.
Import Smten.Smten.
Import SmtenProp.SmtenProp.
Import SmtenS1.SmtenS1.

Inductive valueS : tm -> Prop :=
  | vS_empty : forall T, valueS (temptyS T)
  | vS_single : forall t, valueS (tsingleS t)
  .

Tactic Notation "valueS_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "vS_empty" | Case_aux c "vS_single" ].

Hint Constructors valueS.

Reserved Notation "t1 '=S=>' t2" (at level 40).

Inductive stepS : tm -> tm -> Prop :=
  | STS_STS1 : forall t t',
      t =S1=> t' ->
      t =S=> t'
  | STS_UnionLeft : forall t1 t2,
      tunionS (tsingleS t1) t2 =S=> tsingleS t1
  | STS_UnionRight : forall t1 t2,
      tunionS t1 (tsingleS t2) =S=> tsingleS t2
  | STS_UnionNotRight : forall T t,
      tunionS t (temptyS T) =S=> t
  | STS_UnionNotLeft : forall T t,
      tunionS (temptyS T) t =S=> t
  | STS_Union1 : forall t1 t1' t2,
      t1 =S=> t1' ->
      tunionS t1 t2 =S=> tunionS t1' t2
  | STS_Union2 : forall t1 t2 t2',
      t2 =S=> t2' ->
      tunionS t1 t2 =S=> tunionS t1 t2'

where "t1 '=S=>' t2" := (stepS t1 t2).

Tactic Notation "stepS_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STS_STS1"
  | Case_aux c "STS_UnionLeft" | Case_aux c "STS_UnionRight"
  | Case_aux c "STS_UnionNotRight" | Case_aux c "STS_UnionNotLeft"
  | Case_aux c "STS_Union1" | Case_aux c "STS_Union2" ].

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
  Case "T_UnionS".
     right. destruct IHHt1...
     SCase "t1 is a valueS".
       inversion H.
       SSCase "t1 is emptyS".
          exists t2. apply STS_UnionNotLeft.
       SSCase "t1 is singleS".
          exists (tsingleS t). apply STS_UnionLeft.
     SCase "t1 steps".
       inversion H as [t1'].
       exists (tunionS t1' t2).
       apply STS_Union1...
  Case "T_MapS".
     right. destruct (progressS1 t2 (TS T1))...
     SCase "t2 is a valueS1".
       inversion H.
       SSCase "t2 is emptyS".
         exists (temptyS T2). apply STS_STS1. apply STS1_MapEmpty.
         rewrite <- H0 in Ht2. inversion Ht2...
       SSCase "t2 is singleS".
         exists (tsingleS (tapp t1 t)). apply STS_STS1. apply STS1_MapSingle.
       SSCase "t2 is unionS".
         exists (tunionS (tmapS t1 t0) (tmapS t1 t3)).
         apply STS_STS1. apply STS1_MapUnion.
     SCase "t1 steps".
       inversion H as [t2'].
       exists (tmapS t1 t2').
       apply STS_STS1. apply STS1_Map. assumption.
  Case "T_JoinS".
     right. destruct (progressS1 t (TS (TS T)))...
     SCase "t is a valueS1".
       inversion H.
       SSCase "t is emptyS".
         subst. inversion Ht.
         exists (temptyS T). apply STS_STS1. apply STS1_JoinEmpty.
       SSCase "t is singleS".
         exists (t0). apply STS_STS1. apply STS1_JoinSingle.
       SSCase "t is unionS".
         exists (tunionS (tjoinS t1) (tjoinS t2)).
         apply STS_STS1. apply STS1_JoinUnion.
     SCase "t steps".
       inversion H as [t'].
       exists (tjoinS t').
       apply STS_STS1. apply STS1_Join. assumption.
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
   Case "STS_UnionLeft". inversion HT...
   Case "STS_UnionRight". inversion HT...
   Case "STS_UnionNotRight". inversion HT...
   Case "STS_UnionNotLeft". inversion HT...
   Case "STS_Union1". inversion HT...
   Case "STS_Union2". inversion HT...
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
  | Un_Empty : forall T, unsat (temptyS T)
  | Un_Step : forall t T,
      empty |- t \in TS T ->
      (exists t', t =S=> t') ->
      (forall t', t =S=> t' -> unsat t') ->
      unsat t
  .

Tactic Notation "unsat_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Un_Empty" | Case_aux c "Un_Step" ].

Hint Constructors unsat.

Theorem unsat_goes_zero : forall t T,
  empty |- t \in TS T ->
  unsat t ->
  t =S=>* temptyS T
  .
Proof.
  intros t T HT Hunsat.
  unsat_cases (induction Hunsat) Case.
  Case "Un_Empty".
    inversion HT.
    apply multi_refl.
  Case "Un_Step".
    destruct (progressS t (TS T)). assumption.
    exists T. reflexivity.
    SCase "t is a valueS".
      valueS_cases (inversion H3) SSCase.
      SSCase "vS_empty".
        rewrite <- H4 in HT.
        inversion HT.
        apply multi_refl.
      SSCase "vS_single".
        inversion H0.
        rewrite <- H4 in H5.
        inversion H5. inversion H6. inversion H9.      
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
  Case "Un_Empty".
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
  tv = temptyS T
  .
Proof.
  intros t tv T HT Hunsat Hsteps Hval.
  assert (unsat tv).
  apply unsat_preserves_multi with t T.
  assumption. assumption. assumption.
  valueS_cases (destruct Hval) Case.
  Case "vS_empty".
    f_equal.
    assert (empty |- temptyS T0 \in TS T).
    apply preservationS_multi with t.
    assumption. assumption.
    inversion H0. reflexivity.
  Case "vS_single".
    inversion H.
    inversion H1. inversion H4. inversion H5. inversion H8.
Qed.

Theorem unsat_union_unsat_zero : forall t T,
  empty |- t \in TS T ->
  unsat t ->
  unsat (tunionS t (temptyS T))
  .
Proof.
  intros t T HT Hunsat.
  unsat_cases (induction Hunsat) Case.
  Case "Un_Empty".
    apply Un_Step with T.
    apply T_UnionS. assumption. apply T_EmptyS.
    exists (temptyS T). apply STS_UnionNotLeft.
    intros tv Hstep.
    inversion Hstep.
    SCase "Pure". inversion H. inversion H2.
    SCase "UnionNotRight". apply Un_Empty.
    SCase "UnionNotLeft". apply Un_Empty.
    SCase "Union1". inversion H2. inversion H3. inversion H6.
    SCase "Union2". inversion H2. inversion H3. inversion H6.
  Case "Un_Step".
    apply Un_Step with T.
    apply T_UnionS. assumption. apply T_EmptyS.
    exists t. apply STS_UnionNotRight.
    intros tv Hstep.
    inversion Hstep.
    SCase "Pure". inversion H3. inversion H6.
    SCase "UnionLeft".
      inversion H0.
      rewrite <- H4 in H6. inversion H6. inversion H7. inversion H10.
    SCase "UnionNotRight".
      rewrite <- H3.
      apply Un_Step with T.
      assumption. assumption. assumption.
    SCase "UnionNotLeft". apply Un_Empty.
    SCase "Union1".
      apply H2. assumption. 
      apply preservationS with t. assumption. assumption.
    SCase "Union2". inversion H6. inversion H7. inversion H10.
Qed.

Theorem unsat_union_if : forall t1 t2 T,
  empty |- t1 \in TS T ->
  empty |- t2 \in TS T ->
  unsat t1 ->
  unsat t2 ->
  unsat (tunionS t1 t2)
  .
Proof.
  intros t1 t2 T HT1  HT2 Hunsat1 Hunsat2.
  generalize dependent t2.
  unsat_cases (induction Hunsat1) Case; intros t2 HT2 Hunsat2.
  Case "Un_Empty".
    unsat_cases (induction Hunsat2) SCase.
    SCase "Un_Empty".
      apply unsat_union_unsat_zero.
      inversion HT1.
      inversion HT2.
      apply T_EmptyS.
      apply Un_Empty.
    SCase "Un_Step".
      apply Un_Step with T.
      apply T_UnionS. assumption. assumption.
      exists t. apply STS_UnionNotLeft.
      intros tv Hstep.
      inversion Hstep.
      SSCase "Pure". inversion H3. inversion H6.
      SSCase "UnionLeft".
        inversion H0.
        rewrite <- H5 in H6. inversion H6. inversion H7. inversion H10.
      SSCase "UnionNotRight". apply Un_Empty.
      SSCase "UnionNotLeft".
        rewrite <- H3.
        apply Un_Step with T.
        assumption. assumption. assumption.
      SSCase "Union1". inversion H6. inversion H7. inversion H10.
      SSCase "Union2".
        apply H2. assumption. 
        apply preservationS with t. assumption. assumption.
   Case "Un_Step".
     unsat_cases (induction Hunsat2) SCase.
     SCase "Un_Empty".
       apply unsat_union_unsat_zero.
       inversion HT2. assumption.
       apply Un_Step with T. assumption. assumption. assumption.
     SCase "Un_Step".
       apply Un_Step with T.
       apply T_UnionS. assumption. assumption.
       inversion H0 as [t2].
       exists (tunionS t2 t0). apply STS_Union1. assumption.
       intros tv Hstep.
       inversion Hstep.
       SSCase "Pure". inversion H7. inversion H10.
       SSCase "UnionLeft". 
         rewrite <- H8 in H0.
         inversion H0.
         inversion H10. inversion H11. inversion H14.
       SSCase "UnionRight".
         rewrite <- H9 in H4.
         inversion H4. inversion H10. inversion H11. inversion H14.
       SSCase "UnionNotRight".
         rewrite <- H7.
         apply Un_Step with T.
         assumption. assumption. assumption.
       SSCase "UnionNotLeft".
         rewrite <- H7.
         apply Un_Step with T; assumption.
       SSCase "Union1".
         apply H2. assumption.
         apply preservationS with t. assumption. assumption. assumption.
         apply Un_Step with T; assumption.
       SSCase "Union2".
         apply H6. assumption.
         apply preservationS with t0; assumption.
Qed.

Theorem unsat_union_only : forall t t1 t2 T,
  empty |- t \in TS T ->
  unsat t ->
  t = tunionS t1 t2 ->
  unsat t1 /\ unsat t2
  .
Proof.
  intros t t1 t2 T HT Hunsat Hdef.
  generalize dependent t2.
  generalize dependent t1.
  unsat_cases (induction Hunsat) Case; intros t1 t2 Hdef.
  Case "Un_Empty". inversion Hdef.
  Case "Un_Step".
    rewrite Hdef in *. clear Hdef.
    split.
    destruct (progressS t1) with (TS T).
    inversion HT. assumption. exists T. reflexivity.
    SCase "valueS t1".
      valueS_cases (destruct H3) SSCase.
      SSCase "vS_empty". apply Un_Empty.
      SSCase "vS_single".
        apply H1.
        apply STS_UnionLeft.
    SCase "t1 steps".
      apply Un_Step with T.
      inversion HT. assumption.
      assumption.
      intros tv Hstep.

      assert (Hpstep : tunionS t1 t2 =S=> tunionS tv t2).
      apply STS_Union1. assumption.

      assert (HpT : empty |- (tunionS tv t2) \in TS T).
      inversion HT.
      apply T_UnionS.
      apply preservationS with t1.
      assumption. assumption. assumption.

      assert (Hpeq : tunionS tv t2 = tunionS tv t2).
      reflexivity.

      specialize (H2 (tunionS tv t2) Hpstep HpT tv t2 Hpeq).
      decompose [and] H2.
      assumption.
     
    destruct (progressS t2) with (TS T).
    inversion HT. assumption. exists T. reflexivity.
    SCase "valueS t2".
      valueS_cases (destruct H3) SSCase.
      SSCase "vS_empty". apply Un_Empty.
      SSCase "vS_single".
        apply H1.
        apply STS_UnionRight.
    SCase "t2 steps".
      apply Un_Step with T.
      inversion HT. assumption.
      assumption.
      intros tv Hstep.

      assert (Hpstep : tunionS t1 t2 =S=> tunionS t1 tv).
      apply STS_Union2. assumption.

      assert (HpT : empty |- (tunionS t1 tv) \in TS T).
      inversion HT.
      apply T_UnionS.
      assumption.
      apply preservationS with t2.
      assumption. assumption.

      assert (Hpeq : tunionS t1 tv = tunionS t1 tv).
      reflexivity.

      specialize (H2 (tunionS t1 tv) Hpstep HpT t1 tv Hpeq).
      decompose [and] H2.
      assumption.
Qed.

Theorem union1_multi : forall t1 t1' t2 T,
  empty |- t1 \in TS T ->
  empty |- t2 \in TS T ->
  t1 =S=>* t1' ->
  tunionS t1 t2 =S=>* tunionS t1' t2
  .
Proof.    
  intros t1 t1' t2 T HT1 HT2 Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". apply multi_refl.
  Case "multi_step". 
    apply multi_step with (tunionS y0 t2).
    apply STS_Union1. assumption.
    apply IHHsteps.
    apply preservationS with x0; assumption.
Qed.

Theorem union2_multi : forall t1 t2 t2' T,
  empty |- t1 \in TS T ->
  empty |- t2 \in TS T ->
  t2 =S=>* t2' ->
  tunionS t1 t2 =S=>* tunionS t1 t2'
  .
Proof.    
  intros t1 t2 t2' T HT1 HT2 Hsteps.
  multi_cases (induction Hsteps) Case.
  Case "multi_refl". apply multi_refl.
  Case "multi_step". 
    apply multi_step with (tunionS t1 y0).
    apply STS_Union2. assumption.
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
  Case "temptyS". sts1_det (temptyS t) t' T.
  Case "tsingleS". sts1_det (tsingleS t) t' T.
  Case "tunionS".
    inversion Hstep.
    SCase "S1". inversion H. inversion H2.
    SCase "UnionLeft". (* but tsingle is not unsat *)
      rewrite <- H2 in Hunsat.
      inversion Hunsat.
      inversion H3. inversion H6. inversion H7. inversion H10.
    SCase "UnionRight". (* but tsingle is not unsat *)
      rewrite <- H2 in Hunsat.
      inversion Hunsat.
      inversion H3. inversion H6. inversion H7. inversion H10.
    SCase "UnionNotRight".
      apply unsat_union_if with T.
      apply preservationS with (tunionS t1 t2) . assumption. assumption.
      rewrite H1. inversion HT. assumption. assumption.
      apply Un_Empty.
    SCase "UnionNotLeft".
      apply unsat_union_if with T.
      rewrite H0.
      inversion HT. assumption.
      apply preservationS with (tunionS t1 t2). assumption. assumption.
      apply Un_Empty. assumption.
    SCase "Union1".
      rewrite <- H0 in Hunsat.
      inversion HT.
      assert (empty |- t1' \in TS T).
      apply preservationS with t1; assumption.
    
      assert (unsat t1').
      apply proj1 with (unsat t2).
      apply unsat_union_only with (tunionS t1' t2) T.
      apply T_UnionS ; assumption.
      assumption. reflexivity.

      assert (unsat t1).
      apply IHt1 with t1' T; assumption.
 
      assert (tunionS t1' t2 =S=>* tunionS (temptyS T) t2).
      apply union1_multi with T ;
      [ assumption | assumption | apply unsat_goes_zero ; assumption ].
      
      assert (unsat (tunionS (temptyS T) t2)).
      apply unsat_preserves_multi with (tunionS t1' t2) T.
      apply T_UnionS; assumption. assumption. assumption.

      assert (unsat t2).
      apply unsat_preserves with (tunionS (temptyS T) t2) T.
      apply T_UnionS . apply T_EmptyS. assumption.
      assumption.
      apply STS_UnionNotLeft.
      
      apply unsat_union_if with T; assumption.

    SCase "Union2".
      rewrite <- H0 in Hunsat.
      inversion HT.
      assert (empty |- t2' \in TS T).
      apply preservationS with t2; assumption.
    
      assert (unsat t2').
      apply proj2 with (unsat t1).
      apply unsat_union_only with (tunionS t1 t2') T.
      apply T_UnionS ; assumption.
      assumption. reflexivity.

      assert (unsat t2).
      apply IHt2 with t2' T; assumption.
 
      assert (tunionS t1 t2' =S=>* tunionS t1 (temptyS T)).
      apply union2_multi with T ;
      [ assumption | assumption | apply unsat_goes_zero ; assumption ].
      
      assert (unsat (tunionS t1 (temptyS T))).
      apply unsat_preserves_multi with (tunionS t1 t2') T.
      apply T_UnionS; assumption. assumption. assumption.

      assert (unsat t1).
      apply unsat_preserves with (tunionS t1 (temptyS T)) T.
      apply T_UnionS . assumption. apply T_EmptyS.
      assumption.
      apply STS_UnionNotRight.
      
      apply unsat_union_if with T; assumption.
  Case "tmapS". sts1_det (tmapS t1 t2) t' T.
  Case "tjoinS". sts1_det (tjoinS t) t' T.
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
   t1 =S=>* temptyS T ->
   t1 =S=>* t2 ->
   valueS t2 ->
   t2 = temptyS T
  .
Proof.
   intros t1 t2 T HT Htozero Htot2 Hvt2.
   apply unsat_goes_only_zero with t1.
   assumption.
   apply unsat_expands_multi with (temptyS T) T.
   assumption.
   apply Un_Empty. assumption. assumption. assumption.
Qed.   
  
End SmtenS.

