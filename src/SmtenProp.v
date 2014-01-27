
Require Export SfLib.
Require Export Smten.

Module SmtenProp.
Import Smten.Smten.

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
  Case "T_Case".
    assert (TArrow T1 T3 = TArrow T0 Tb)...
    injection H7...
  Case "T_Fix".
    assert (TArrow T T = TArrow Tb Tb)...
    injection H3...
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
Qed.

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma.
  Ltac isvalue v_xx := left ; apply v_xx.
  Case "T_Var".
    (* contradiction: variables aren't typed in empty context *)
    unfold empty in H ; discriminate H.
  Case "T_Abs". isvalue v_abs.
  Case "T_App".
    (* t1 t2.
       If t1 steps, then we make progress with ST_App,
       otherwise, t1 must be an abstraction, so we make progress with ST_AppAbs.
    *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_abs".
        exists ([x0:=t2]t).
        apply ST_AppAbs ; assumption.
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tapp t1' t2).
      apply ST_App ; assumption.
  Case "T_Unit". isvalue v_unit.
  Case "T_Pair". isvalue v_pair.
  Case "T_Fst".
    (* fst t
       If t steps, then we make progress with ST_Fst,
       otherwise, t must be a pair, so we make progress with ST_FstPair.
    *)
    right. destruct IHHt...
    SCase "t is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_pair".
        exists t1.
        apply ST_FstPair ; assumption.
    SCase "t steps".
      inversion H as [t' Hstp].
      exists (tfst t').
      apply ST_Fst ; assumption.

  Case "T_Snd".
    (* snd t
       If t steps, then we make progress with ST_Snd,
       otherwise, t must be a pair, so we make progress with ST_SndPair.
    *)
    right. destruct IHHt...
    SCase "t is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_pair".
        exists t2.
        apply ST_SndPair ; assumption.
    SCase "t steps".
      inversion H as [t' Hstp].
      exists (tsnd t').
      apply ST_Snd ; assumption.
  Case "T_Inl". isvalue v_inl.
  Case "T_Inr". isvalue v_inr.
  Case "T_Case".
    (* case t1 t2 t3
       If t1 steps, then we make progress with ST_Case,
       otherwise, t must be inl or inr, so we make progress with
       ST_CaseInl or ST_CaseInr.
    *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_inl".
        exists (tapp t2 t).
        apply ST_CaseInl ; assumption.
      SSCase "v_inr".
        exists (tapp t3 t).
        apply ST_CaseInr ; assumption.
    SCase "t1 steps".
      inversion H as [t1' Hstp].
      exists (tcase t1' t2 t3).
      apply ST_Case ; assumption.
  Case "T_Fix".
    (* makes progress by ST_Fix *)
    right.
    exists (tapp t (tfix t)).
    apply ST_Fix ; assumption.
  Case "T_ReturnIO". isvalue v_returnIO.
  Case "T_BindIO". isvalue v_bindIO.
  Case "T_SearchIO". isvalue v_searchIO.
  Case "T_ReturnS". isvalue v_returnS.
  Case "T_BindS". isvalue v_bindS.
  Case "T_ZeroS". isvalue v_zeroS.
  Case "T_PlusS". isvalue v_plusS.
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
  .

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_pair1" | Case_aux c "afi_pair2"
  | Case_aux c "afi_fst" | Case_aux c "afi_snd" 
  | Case_aux c "afi_inl" | Case_aux c "afi_inr"
  | Case_aux c "afi_case1" | Case_aux c "afi_case2"
  | Case_aux c "afi_case3" | Case_aux c "afi_fix" 
  | Case_aux c "afi_returnIO"
  | Case_aux c "afi_bindIO1" | Case_aux c "afi_bindIO2"
  | Case_aux c "afi_searchIO"
  | Case_aux c "afi_returnS"
  | Case_aux c "afi_bindS1" | Case_aux c "afi_bindS2"
  | Case_aux c "afi_plusS1" | Case_aux c "afi_plusS2"
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
  Ltac doesnt_step := inversion HE.
  has_type_cases (induction HT) Case;
       intros t' HE; subst.
  Case "T_Var". doesnt_step.
  Case "T_Abs". doesnt_step.
  Case "T_App".
    inversion HE; subst.
    SCase "ST_AppAbs".
      (* substitution preserves typing *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
    SCase "ST_App".
      (* t1' t2
         By induction, t1' has the same type as t1, so
         t1' t2 has the same type as t1' t2.
      *)
      apply T_App with T11 .
      apply IHHT1. reflexivity. assumption. assumption.
  Case "T_Unit". doesnt_step.
  Case "T_Pair". doesnt_step.
  Case "T_Fst".
    inversion HE; subst...
    inversion HT; subst...
  Case "T_Snd".
    (* ST_SndPair: snd (t1, t2) steps to t2
       ST_Snd: snd t steps to snd t'
         t goes to t', which has the same type as t by induction.
         Then snd t' has the same type as snd t.
    *)
    inversion HE; subst.
    SCase "ST_SndPair".
      inversion HT ; subst. assumption.
    SCase "ST_Snd".
      apply T_Snd with T1;
      apply IHHT; [ reflexivity | assumption].
  Case "T_Inl". doesnt_step.
  Case "T_Inr". doesnt_step.
  Case "T_Case".
    (* ST_CaseInl: case (inl t1) t2 t3 steps to (t2 t1)
         t2 has type T1 -> T3, and t1 has type T1, so (t2 t1) has type T3.
       ST_CaseInr: case (inr t1) t2 t3 steps to (t3 t1)
         t3 has type T2 -> T3, and t1 has type T2, so (t3 t1) has type T3.
       ST_Case: case t1 t2 t3 steps to case t1' t2 t3
         t1 goes to t1', which has the same type as t1 by induction.
         Then case t1' t2 t3 has the same type as t1.
    *)
    remember (tcase t1 t2 t3) as t eqn:Hdeft.
    step_cases (destruct HE) SCase ; subst ; try discriminate Hdeft.
    SCase "ST_CaseInl".
      injection Hdeft. intros. subst.
      inversion HT1; subst;
      apply T_App with T1 ; assumption.
    SCase "ST_CaseInr".
      injection Hdeft. intros. subst.
      inversion HT1; subst;
      apply T_App with T2 ; assumption.
    SCase "ST_Case".
      injection Hdeft. intros. subst.
      apply T_Case with T1 T2 ;
      [ apply IHHT1; [ reflexivity | assumption]
      | assumption
      | assumption].
  Case "T_Fix".
    (* tfix t must step to (tapp t (tfix t)),
       and because (tfix t) has type T, and t has type T -> T,
       (tapp t (tfix t)) also has type T.
    *)
    inversion HE. subst.
    apply T_App with T; [ assumption | apply T_Fix ; assumption].
  Case "T_ReturnIO". doesnt_step.
  Case "T_BindIO". doesnt_step.
  Case "T_SearchIO". doesnt_step.
  Case "T_ReturnS". doesnt_step.
  Case "T_BindS". doesnt_step.
  Case "T_ZeroS". doesnt_step.
  Case "T_PlusS". doesnt_step.
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
   Case "tcase".
      SCase "case inl".
        rewrite <- H0 in Hstep2.
        inversion Hstep2.
        SSCase "case inl". reflexivity.
        SSCase "case". inversion H7.
      SCase "case inr".
        rewrite <- H0 in Hstep2.
        inversion Hstep2.
        SSCase "case inr". reflexivity.
        SSCase "case". inversion H7.
      SCase "case".
        inversion Hstep2.
        SSCase "case inl".
          rewrite <- H5 in H3. inversion H3.
        SSCase "case inr".
          rewrite <- H5 in H3. inversion H3.
        SSCase "case".
          f_equal.
          inversion HT.
          apply IHt1 with (TSum T1 T2).
          assumption. assumption. assumption.
   Case "tfix".
     inversion Hstep2.
     reflexivity.
Qed.

End SmtenProp.

