
Require Export SfLib.
Require Export Smimpl.

Module SmimplProp.
Import Smimpl.Smimpl.

Theorem unique_typing : forall Gamma t T1 T2,
    Gamma |- t \in T1 ->
    Gamma |- t \in T2 ->
    T1 = T2 .

Proof with auto.
  intros Gamma t Ta Tb HTa HTb.
  generalize dependent Tb.
  has_type_cases (induction HTa) Case ; intros Tb HTb; inversion HTb.
  Case "T_Var". rewrite H in H2. injection H2. auto.
  Case "T_Abs".
    assert (T12 = T1).
    apply IHHTa. assumption.
    rewrite H5. reflexivity.
  Case "T_App".
    assert (TArrow T11 T12 = TArrow T0 Tb). apply IHHTa1. assumption.
    injection H5. auto.
  Case "T_Unit". reflexivity.
  Case "T_Pair".
    f_equal.
    apply IHHTa1...
    apply IHHTa2...
  Case "T_Fst".
    assert (TProd T1 T2 = TProd Tb T3).
    apply IHHTa...
    injection H3...
  Case "T_Snd".
    assert (TProd T1 T2 = TProd T0 Tb).
    apply IHHTa...
    injection H3...
  Case "T_Inl".
    f_equal. 
    apply IHHTa...
  Case "T_Inr".
    f_equal. apply IHHTa...
  Case "T_Sum".
    f_equal.
    apply IHHTa1. assumption.
    apply IHHTa2. assumption.
  Case "T_Case".
    assert (TArrow T1 T3 = TArrow T0 Tb)...
    injection H7...
  Case "T_Fix".
    assert (TArrow T T = TArrow Tb Tb)...
    injection H3...
  Case "T_Ite".
    apply IHHTa1. assumption.
  Case "T_ReturnIO".
    f_equal. apply IHHTa...
  Case "T_BindIO".
    f_equal.
    assert (TArrow T1 (TIO T2) = TArrow T0 (TIO T3))...
    injection H5...
  Case "T_SearchIO".
    f_equal.
    assert (TS T = TS T0)...
    injection H3. intro.
    rewrite H4. reflexivity.
  Case "T_IteIO". apply IHHTa1. assumption. 
  Case "T_ReturnS".
    f_equal. apply IHHTa...
  Case "T_BindS".
    f_equal.
    assert (TArrow T1 (TS T2) = TArrow T0 (TS T3))...
    injection H5...
  Case "T_ZeroS". reflexivity.
  Case "T_PlusS".
    f_equal.
    assert (TS T = TS T0)...
    injection H5...
  Case "T_SetS". 
    f_equal.
    apply IHHTa. assumption.
  Case "T_IteS".
    apply IHHTa1. assumption.
Qed.

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".  (* contradictory: variables cannot be typed in an empty context *)
    unfold empty in H. discriminate H.

  Case "T_App". 
    right. (* We will show we always can make progress *)
    destruct IHHt1... (* by case on whether the function t1 is a value or steps *)
    SCase "t1 is a value".
      (* The only value with function type is v_abs, in which case ST_AppAbs applies *)
      remember (TArrow T11 T12) as TF eqn:HdefTF.
      remember t1 as tf eqn:Hdeftf.
      Ltac nonfunction_value Hdeftf Ht1 :=
             rewrite Hdeftf in Ht1 ; destruct Ht1 ; discriminate .
      v_cases (destruct H) SSCase .
      SSCase "v_abs"; exists ([x0:=t2]t); apply ST_AppAbs.
      SSCase "v_unit". nonfunction_value Hdeftf Ht1.
      SSCase "v_pair". nonfunction_value Hdeftf Ht1.
      SSCase "v_sum". nonfunction_value Hdeftf Ht1.
      SSCase "v_IO". destruct H ; nonfunction_value Hdeftf Ht1.
      SSCase "v_S". destruct H ; nonfunction_value Hdeftf Ht1.

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_Fst".
    right. destruct IHHt...

    SCase "t is a value".
      (* Since [t] is a value of product type, it must
         be a pair *)
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_pair". eauto.
      SSCase "v_IO". inversion H0; subst; try solve by inversion.
      SSCase "v_S". inversion H0; subst; try solve by inversion.


    SCase "t also steps".
      inversion H as [t' Hstp]. exists (tfst t')...

  Case "T_Snd".
    right. destruct IHHt...

    SCase "t is a value".
      (* Since [t] is a value of product type, it must
         be a pair *)
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_pair". eauto.
      SSCase "v_IO". inversion H0; subst; try solve by inversion.
      SSCase "v_S". inversion H0; subst; try solve by inversion.

    SCase "t also steps".
      inversion H as [t' Hstp]. exists (tsnd t')...

  Case "T_Case".
    right. destruct IHHt1...

    SCase "t1 is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_sum". eauto.
      SSCase "v_IO". inversion H0; subst; try solve by inversion.
      SSCase "v_S". inversion H0; subst; try solve by inversion.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tcase t1' t2 t3)...
 
  Case "T_Ite".
    right. destruct IHHt1...

    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is a value".
        v_cases (inversion H) SSSCase.
        SSSCase "v_abs".
           v_cases (inversion H0) SSSSCase;
              subst ; inversion Ht2 ; subst ; inversion Ht1 ; try (inversion H2).
           SSSSCase "v_abs".
             subst.
             exists (tabs x T1 (tite p (tapp (tabs x0 T1 t) (tvar x)) (tapp (tabs x1 T1 t0) (tvar x)))).
             apply ST_IteAbs.
        SSSCase "v_unit".
           v_cases (inversion H0) SSSSCase;
             subst ; inversion Ht2 ; subst ; inversion Ht1 ; try (inversion H2).
           SSSSCase "v_unit".
             exists tunit. apply ST_IteUnit.
        SSSCase "v_pair".
           v_cases (inversion H0) SSSSCase;
             subst ; inversion Ht2 ; subst ; inversion Ht1 ; try (inversion H2).
           SSSSCase "v_pair". subst.
             exists (tpair (tite p t0 t4) (tite p t3 t5)).
             apply ST_ItePair.
        SSSCase "v_sum".
           v_cases (inversion H0) SSSSCase;
             subst ; inversion Ht2 ; subst ; inversion Ht1 ; try (inversion H2).
           SSSSCase "v_sum". subst.
             exists (tsum (Sat.fite p p0 p1) (tite p t0 t4) (tite p t3 t5)).
             apply ST_IteSum.
        SSSCase "v_IO".
           v_cases (inversion H0) SSSSCase.
           SSSSCase "v_abs". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_unit". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_pair". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_sum". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_IO".
             exists (titeIO p t1 t2). apply ST_IteIO; assumption.
           SSSSCase "v_S".
             inversion H1; subst;
             inversion H3; subst;
             inversion Ht1; subst ; inversion Ht2.
        SSSCase "v_S".
           v_cases (inversion H0) SSSSCase.
           SSSSCase "v_abs". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_unit".
             subst.
             remember tunit as t eqn:Heq.
             has_type_cases (destruct Ht2) SSSSSCase ; try discriminate Heq.
             SSSSSCase "T_Unit".
               (* no svalue t1 has type TUnit *)
               remember t1 as tx eqn:Heqtx ;
               destruct H1 ;
                rewrite Heqtx in Ht1 ;
                remember TUnit as Tval eqn:HeqT ;
                destruct Ht1 ;
                 try discriminate HeqT ; try discriminate Heqtx.

           SSSSCase "v_pair". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_sum". inversion H1 ; subst ; inversion Ht2 ; subst ; inversion Ht1.
           SSSSCase "v_IO".
             inversion H1; subst;
             inversion H3; subst;
             inversion Ht1; subst ; inversion Ht2.
           SSSSCase "v_S".
             exists (titeS p t1 t2). apply ST_IteS; assumption.
      SSCase "t2 steps".
        inversion H0 as [t2'].
        exists (tite p t1 t2').
        apply ST_Ite2; assumption.
    SCase "t1 steps".
      inversion H as [t1'].
      exists (tite p t1' t2).
      apply ST_Ite1; assumption.

Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tpair t1 t2)
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tpair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (tfst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsnd t)
  | afi_inl : forall x T t,
      appears_free_in x t ->
      appears_free_in x (tinl T t)
  | afi_inr : forall x T t,
      appears_free_in x t ->
      appears_free_in x (tinr T t)
  | afi_sum1 : forall x p t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tsum p t1 t2)
  | afi_sum2 : forall x p t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tsum p t1 t2)
  | afi_case1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tcase t1 t2 t3)
  | afi_case2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tcase t1 t2 t3)
  | afi_case3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tcase t1 t2 t3)
  | afi_fix : forall x t,
      appears_free_in x t ->
      appears_free_in x (tfix t)
  | afi_ite1 : forall x p t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tite p t1 t2)
  | afi_ite2 : forall x p t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tite p t1 t2)
  | afi_returnIO : forall x t,
      appears_free_in x t ->
      appears_free_in x (treturnIO t)
  | afi_bindIO1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tbindIO t1 t2)
  | afi_bindIO2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tbindIO t1 t2)
  | afi_searchIO : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsearchIO t)
  | afi_iteIO1 : forall x p t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (titeIO p t1 t2)
  | afi_iteIO2 : forall x p t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (titeIO p t1 t2)
  | afi_returnS : forall x t,
      appears_free_in x t ->
      appears_free_in x (treturnS t)
  | afi_bindS1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tbindS t1 t2)
  | afi_bindS2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tbindS t1 t2)
  | afi_plusS1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tplusS t1 t2)
  | afi_plusS2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tplusS t1 t2)
  | afi_setS : forall x p t,
      appears_free_in x t ->
      appears_free_in x (tsetS p t)
  | afi_iteS1 : forall x p t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (titeS p t1 t2)
  | afi_iteS2 : forall x p t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (titeS p t1 t2)
  .

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_pair1" | Case_aux c "afi_pair2"
  | Case_aux c "afi_fst" | Case_aux c "afi_snd" 
  | Case_aux c "afi_inl" | Case_aux c "afi_inr"
  | Case_aux c "afi_sum1" | Case_aux c "afi_sum2"
  | Case_aux c "afi_case1" | Case_aux c "afi_case2"
  | Case_aux c "afi_case3" | Case_aux c "afi_fix" 
  | Case_aux c "afi_ite1" | Case_aux c "afi_ite2"
  | Case_aux c "afi_returnIO"
  | Case_aux c "afi_bindIO1" | Case_aux c "afi_bindIO2"
  | Case_aux c "afi_searchIO"
  | Case_aux c "afi_iteIO1" | Case_aux c "afi_iteIO2"
  | Case_aux c "afi_returnS"
  | Case_aux c "afi_bindS1" | Case_aux c "afi_bindS2"
  | Case_aux c "afi_plusS1" | Case_aux c "afi_plusS2"
  | Case_aux c "afi_setS"
  | Case_aux c "afi_iteS1" | Case_aux c "afi_iteS2"
  ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

Lemma closed_typing : forall t T,
  empty |- t \in T ->
  closed t.
Proof.
  intros t T HT.
  unfold closed.
  intro x.
  unfold not.
  intro Hafi.
  absurd (exists (T':ty), empty x = Some T').
  unfold not. intro Hsilly. inversion Hsilly. inversion H.
  apply free_in_context with t T; assumption.
Qed.
  

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.

Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App". apply T_App with T11...
  Case "T_Fst". apply T_Fst with T2...
  Case "T_Snd". apply T_Snd with T1...
  Case "T_Case". apply T_Case with T1 T2...
  Case "T_BindIO". apply T_BindIO with T1...
  Case "T_BindS". apply T_BindS with T1...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.

Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T. 
  t_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id... 
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.

Proof with eauto.
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...
  Case "T_Fst".
    inversion HE; subst...
    inversion HT; subst...
  Case "T_Snd".
    inversion HE; subst...
    inversion HT; subst...
  Case "T_Case".
    inversion HE; subst...
    SCase "inl". inversion HT1; subst...
  Case "T_Fix".
    inversion HE; subst...
  Case "T_Ite".
    inversion HE; subst...
    SCase "tabs".
      inversion HT1; subst...
      apply T_Abs.
      apply T_Ite.
      apply T_App with T0.
      apply context_invariance with empty.
      assumption.
      intros x0 Hfree.
      absurd (appears_free_in x0 (tabs x1 T0 t0)).
      assert (closed (tabs x1 T0 t0)).
      apply closed_typing with (TArrow T0 T12) ; assumption.
      unfold closed in H.
      specialize H with x0. apply H.
      apply Hfree.
      apply T_Var. auto.

      apply T_App with T0.
      apply context_invariance with empty.
      assumption.
      intros x0 Hfree.
      absurd (appears_free_in x0 (tabs x2 T0 t3)).
      assert (closed (tabs x2 T0 t3)).
      apply closed_typing with (TArrow T0 T12) ; assumption.
      unfold closed in H.
      specialize H with x0. apply H.
      apply Hfree.
      apply T_Var. auto.
    SCase "tpair".
      inversion HT2; subst; inversion HT1; subst.
      apply T_Pair.
      apply T_Ite ; assumption.
      apply T_Ite ; assumption.
    SCase "tsum".
      inversion HT2; subst; inversion HT1; subst.
      apply T_Sum; apply T_Ite ; assumption.
    SCase "io".
      destruct H3; inversion HT1; subst ; apply T_IteIO ; assumption.
    SCase "s".
      destruct H3; inversion HT1; subst ; apply T_IteS ; assumption.
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti. apply Hnot_val. 
   destruct (progress x0 T).
   apply Hhas_type. apply H.
   contradiction.

   apply IHHmulti.
   apply (preservation x0 y0). apply Hhas_type. apply H.
   apply Hnf. apply Hnot_val.
Qed.

Theorem step_deterministic : forall t t1 t2 T,
   empty |- t \in T ->
   t ==> t1 ->
   t ==> t2 ->
   t1 = t2
   .
Proof.
  intro t.
  t_cases (induction t) Case;
    intros ty1 ty2 T HT Hstep1 Hstep2 ; inversion Hstep1.
  Case "tapp".
    SCase "tf = tabs x0 T0 t0".
      rewrite <- H0 in Hstep2.
      inversion Hstep2.
      SSCase "tf = tabs x0 T0 t0". reflexivity.
      SSCase "tf steps". inversion H5.
    SCase "tf steps".
      inversion Hstep2.
      SSCase "tf = tabs".
         rewrite <- H4 in H2.
         inversion H2.
      SSCase "tf steps".
         f_equal.
         inversion HT.
         apply IHt1 with (TArrow T11 T).
         assumption. assumption. assumption.
    Case "tfst". 
      SCase "fst pair".
        rewrite <- H0 in Hstep2.
        rewrite H1 in Hstep2.
        inversion Hstep2.
        SSCase "fst pair". reflexivity.
        SSCase "fst". inversion H2. 
      SCase "fst".
        inversion Hstep2.
        SSCase "fst pair".
          rewrite <- H3 in H0.
          inversion H0.
        SSCase "fst".
          f_equal.
          inversion HT.
          apply IHt with (TProd T T2).
          assumption. assumption. assumption.
    Case "tsnd". 
      SCase "snd pair".
        rewrite <- H0 in Hstep2.
        rewrite H1 in Hstep2.
        inversion Hstep2.
        SSCase "snd pair". reflexivity.
        SSCase "snd". inversion H2. 
      SCase "snd".
        inversion Hstep2.
        SSCase "snd pair".
          rewrite <- H3 in H0.
          inversion H0.
        SSCase "snd".
          f_equal.
          inversion HT.
          apply IHt with (TProd T1 T).
          assumption. assumption. assumption.
   Case "tinl".
      subst.
      inversion Hstep2.
      reflexivity.
   Case "tinr". inversion Hstep2. reflexivity.
   Case "tcase".
      SCase "case sum".
        rewrite <- H0 in Hstep2.
        inversion Hstep2.
        SSCase "case inl". reflexivity.
        SSCase "case". inversion H7.
      SCase "case".
        inversion Hstep2.
        SSCase "case sum".
          rewrite <- H5 in H3. inversion H3.
        SSCase "case".
          f_equal.
          inversion HT.
          apply IHt1 with (TSum T1 T2).
          assumption. assumption. assumption.
   Case "tfix".
     inversion Hstep2.
     reflexivity.
   Case "tite".
     SCase "tite1".
       inversion HT. subst.
       inversion Hstep2 ; subst.
       SSCase "tite1".
         f_equal. subst.
         apply IHt1 with T ; assumption.
       SSCase "tite2".
         inversion H4 ; subst.
         SSSCase "abs". inversion H3.
         SSSCase "unit". inversion H3.
         SSSCase "pair". inversion H3.
         SSSCase "sum". inversion H3.
         SSSCase "io". inversion H ; subst ; inversion H3.
         SSSCase "s". inversion H ; subst ; inversion H3.
       SSCase "ite abs". inversion H3.
       SSCase "ite unit". inversion H3.
       SSCase "ite pair". inversion H3.
       SSCase "ite sum". inversion H3.
       SSCase "ite IO". inversion H4 ; subst ; inversion H3.
       SSCase "ite S". inversion H4 ; subst ; inversion H3.
     SCase "tite2".
       inversion HT. subst.
       inversion Hstep2 ; subst.
       SSCase "tite1".
         inversion H3 ; subst.
         SSSCase "abs". inversion H5.
         SSSCase "unit". inversion H5.
         SSSCase "pair". inversion H5.
         SSSCase "sum". inversion H5.
         SSSCase "io". inversion H ; subst ; inversion H5.
         SSSCase "s". inversion H ; subst ; inversion H5.
       SSCase "tite2".
         f_equal.
         apply IHt2 with T ; assumption.
       SSCase "ite abs". inversion H4.
       SSCase "ite unit". inversion H4.
       SSCase "ite pair". inversion H4.
       SSCase "ite sum". inversion H4.
       SSCase "ite IO". inversion H6 ; subst ; inversion H4.
       SSCase "ite S". inversion H6 ; subst ; inversion H4.
     SCase "ite abs".
       subst.
       inversion Hstep2 ; subst.
       SSCase "ite1". inversion H3.
       SSCase "ite2". inversion H4.
       SSCase "ite abs". reflexivity.
       SSCase "ite io". inversion H3.
       SSCase "ite s". inversion H3.
     SCase "ite unit".
       subst.
       inversion Hstep2 ; subst.
       SSCase "ite1". inversion H3.
       SSCase "ite2". inversion H4.
       SSCase "ite unit". reflexivity.
       SSCase "ite io". inversion H3.
       SSCase "ite s". inversion H3.
     SCase "ite pair".
       subst.
       inversion Hstep2 ; subst.
       SSCase "ite1". inversion H3.
       SSCase "ite2". inversion H4.
       SSCase "ite pair". reflexivity.
       SSCase "ite io". inversion H3.
       SSCase "ite s". inversion H3.
     SCase "ite sum".
       subst.
       inversion Hstep2 ; subst.
       SSCase "ite1". inversion H3.
       SSCase "ite2". inversion H4.
       SSCase "ite sum". reflexivity.
       SSCase "ite io". inversion H3.
       SSCase "ite s". inversion H3.
     SCase "ite io".
       subst.
       inversion Hstep2 ; subst.
       SSCase "ite1". inversion H3 ; subst ; inversion H5.
       SSCase "ite2". inversion H4 ; subst ; inversion H6.
       SSCase "ite abs". inversion H3.
       SSCase "ite unit". inversion H3.
       SSCase "ite pair". inversion H4.
       SSCase "ite sum". inversion H4.
       SSCase "ite io". reflexivity.
       SSCase "ite s". inversion H3 ; subst ; inversion H5.
     SCase "ite s".
       subst.
       inversion Hstep2 ; subst.
       SSCase "ite1". inversion H3 ; subst ; inversion H5.
       SSCase "ite2". inversion H4 ; subst ; inversion H6.
       SSCase "ite abs". inversion H3.
       SSCase "ite unit". inversion H3.
       SSCase "ite pair". inversion H4.
       SSCase "ite sum". inversion H4.
       SSCase "ite io". inversion H3 ; subst ; inversion H5.
       SSCase "ite s". reflexivity.
   
Qed.

End SmimplProp.

