
Require Export SfLib.
Require Export Smtrg.

Module SmtrgProp.
Import Smtrg.Smtrg.

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
  Case "T_Fix".
    assert (TArrow T T = TArrow Tb Tb)...
    injection H3...
  Case "T_Formula". reflexivity.
  Case "T_If". apply IHHTa1 ; assumption.
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
  Case "T_Fix".
    (* makes progress by ST_Fix *)
    right.
    exists (tapp t (tfix t)).
    apply ST_Fix ; assumption.
  Case "T_Formula". isvalue v_formula.
  Case "T_If".
    (* makes progress by one of
       ST_IfAbs, ST_IfUnit, ST_IfPair, ST_IfFormula,
       ST_IfLeft, or ST_IfRight, depending on
       t1 and t2 as being values or stepping,
       which we have by induction
    *)
    right.
    destruct (IHHt1 (eq_refl empty)) as [Hvalue1 | Hsteps1];
    destruct (IHHt2 (eq_refl empty)) as [Hvalue2 | Hsteps2].
    SCase "t1 and t2 values".
      v_cases (destruct Hvalue1) SSCase ;
      (* Both values must have the same type *)
      destruct Hvalue2 ; inversion Ht1 ; inversion Ht2 ; subst ; try discriminate.
      SSCase "v_abs".
        (* We know the argument types match for both lambdas *)
        injection H7; intros ; subst.

        (* So apply ST_IfAbs *)
        exists (tabs x T0 (tif f (tapp (tabs x0 T0 t) (tvar x)) (tapp (tabs x1 T0 t0) (tvar x)))).
        apply ST_IfAbs.
      SSCase "v_unit". exists tunit ; apply ST_IfUnit.
      SSCase "v_pair". exists (tpair (tif f t1 t2) (tif f t0 t3)) ; apply ST_IfPair.
      SSCase "v_formula". exists (tformula (Sat.fite f f0 f1)) ; apply ST_IfFormula.
    SCase "t1 value, t2 steps".
      destruct Hsteps2 as [t2'].
      exists (tif f t1 t2') ; apply ST_IfRight ; assumption.
    SCase "t1 steps, t2 value". 
      destruct Hsteps1 as [t1'].
      exists (tif f t1' t2) ; apply ST_IfLeft ; assumption.
    SCase "t1 steps, t2 steps".
      destruct Hsteps1 as [t1'].
      exists (tif f t1' t2) ; apply ST_IfLeft ; assumption.
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
  | afi_fix : forall x t,
      appears_free_in x t ->
      appears_free_in x (tfix t)
  | afi_if1 : forall x f t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tif f t1 t2)
  | afi_if2 : forall x f t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tif f t1 t2)
  .

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_pair1" | Case_aux c "afi_pair2"
  | Case_aux c "afi_fst" | Case_aux c "afi_snd" 
  | Case_aux c "afi_fix"
  | Case_aux c "afi_if1" | Case_aux c "afi_if2"
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
    (* ST_AppAbs: app (abs x t1) t2 steps to t1[x=t2]
         and substitution preserves typing.
       ST_App: t1 t2 steps to app t1' t2
         By induction, t1' has the same type as t1, so t1' t2 has the
         same type as t1' t2.
    *)
    inversion HE; subst.
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...
    SCase "ST_App".
      apply T_App with T11 ;
      [ apply IHHT1 ; [ reflexivity | assumption ]
      | assumption]. 
  Case "T_Unit". doesnt_step.
  Case "T_Pair". doesnt_step.
  Case "T_Fst".
    (* ST_FstPair: fst (t1, t2) steps to t1
       ST_Fst: fst t steps to fst t'
         t goes to t', which has the same type as t by induction.
         Then fst t' has the same type as fst t.
    *)
    inversion HE; subst.
    SCase "ST_FstPair".
      inversion HT ; subst. assumption.
    SCase "ST_Fst".
      apply T_Fst with T2.
      apply IHHT; [reflexivity | assumption].
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
  Case "T_Fix".
    (* tfix t must step to (tapp t (tfix t)),
       and because (tfix t) has type T, and t has type T -> T,
       (tapp t (tfix t)) also has type T.
    *)
    inversion HE. subst.
    apply T_App with T; [ assumption | apply T_Fix ; assumption].
  Case "T_Formula". doesnt_step.
  Case "T_If".
    inversion HE ; subst.
    SCase "IfAbs".
      inversion HT1 ; subst ; inversion HT2 ; subst.
      apply T_Abs.
      apply T_If.
      apply T_App with T0.
      apply context_invariance with empty.
      apply T_Abs ; assumption.
      
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
      
    SCase "IfUnit". inversion HT2. apply T_Unit.
    SCase "IfPair".
      inversion HT1 ; subst ; inversion HT2; subst.
      apply T_Pair; apply T_If ; assumption.
    SCase "IfFormula". inversion HT1. apply T_Formula.
    SCase "IfLeft".
      apply T_If.
      apply (IHHT1 (eq_refl empty)) ; assumption.
      assumption.
    SCase "IfRight".
      apply T_If.
      assumption.
      apply (IHHT2 (eq_refl empty)) ; assumption.      
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
    (* terms which are values are solved by inversion on Hstep1 *)
    intros ty1 ty2 T HT Hstep1 Hstep2 ; inversion Hstep1 ; subst ; inversion Hstep2 ; subst.
  Case "tapp".
    SCase "tf = tabs x0 T0 t0".
      SSCase "tf = tabs x0 T0 t0". reflexivity.
      SSCase "tf steps". inversion H2. (* tabs can't step *)
    SCase "tf steps".
      SSCase "tf = tabs". inversion H2. (* tabs can't step *)
      SSCase "tf steps". (* by induction, tf steps to the same place *)
         f_equal.
         inversion HT.
         apply IHt1 with (TArrow T11 T) ; assumption.
  Case "tfst". 
    SCase "fst pair".
      SSCase "fst pair". reflexivity.
      SSCase "fst". inversion H0. (* pair can't step *)
    SCase "fst".
      SSCase "fst pair". inversion H0.
      SSCase "fst".
        f_equal.
        inversion HT.
        apply IHt with (TProd T T2) ; assumption.
  Case "tsnd". 
    SCase "snd pair".
      SSCase "snd pair". reflexivity.
      SSCase "snd". inversion H0. 
    SCase "snd".
      SSCase "snd pair". inversion H0.
      SSCase "snd".
        f_equal.
        inversion HT.
        apply IHt with (TProd T1 T) ; assumption.
  Case "tfix". reflexivity.
  Case "tif".
     SCase "IfAbs".
      SSCase "IfAbs". reflexivity.
      SSCase "IfLeft". inversion H3.
      SSCase "IfRight". inversion H4.
     SCase "IfUnit".
      SSCase "IfUnit". reflexivity.
      SSCase "IfLeft". inversion H3.
      SSCase "IfRight". inversion H4.
     SCase "IfPair".
      SSCase "IfPair". reflexivity.
      SSCase "IfLeft". inversion H3.
      SSCase "IfRight". inversion H4.
     SCase "IfFormula".
      SSCase "IfPair". reflexivity.
      SSCase "IfLeft". inversion H3.
      SSCase "IfRight". inversion H4.
     SCase "IfLeft".
      SSCase "IfAbs". inversion H3.
      SSCase "IfUnit". inversion H3.
      SSCase "IfPair". inversion H3.
      SSCase "IfFormula". inversion H3.
      SSCase "IfLeft".
        f_equal.
        inversion HT ; subst.
        apply IHt1 with T ; assumption.
      SSCase "IfRight".
        destruct H4 ; inversion H3.
     SCase "IfRight".
      SSCase "IfAbs". inversion H4.
      SSCase "IfUnit". inversion H4.
      SSCase "IfPair". inversion H4.
      SSCase "IfFormula". inversion H4.
      SSCase "IfLeft". destruct H3 ; inversion H5.
      SSCase "IfRight".
        f_equal.
        inversion HT ; subst.
        apply IHt2 with T ; assumption.
Qed.

End SmtrgProp.

