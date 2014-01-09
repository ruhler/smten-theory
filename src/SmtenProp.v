
Require Export Smten.

Module SmtenProp.
Import Smten.Smten.

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_abs". exists ([x0:=t2]t)...
 
    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_Fst".
    right. destruct IHHt...

    SCase "t is a value".
      (* Since [t] is a value of product type, it must
         be a pair *)
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_pair". eauto.


    SCase "t also steps".
      inversion H as [t' Hstp]. exists (tfst t')...

  Case "T_Snd".
    right. destruct IHHt...

    SCase "t is a value".
      (* Since [t] is a value of product type, it must
         be a pair *)
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_pair". eauto.

    SCase "t also steps".
      inversion H as [t' Hstp]. exists (tsnd t')...

  Case "T_Case".
    right. destruct IHHt1...

    SCase "t1 is a value".
      v_cases (inversion H) SSCase; subst; try solve by inversion.
      SSCase "v_inl". eauto.
      SSCase "v_inr". eauto.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tcase t1' t2 t3)...

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
  | afi_returnio : forall x t,
      appears_free_in x t ->
      appears_free_in x (treturnio t)
  | afi_bindio1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tbindio t1 t2)
  | afi_bindio2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tbindio t1 t2)
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
  | Case_aux c "afi_returnio"
  | Case_aux c "afi_bindio1" | Case_aux c "afi_bindio2" ].

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
  Case "T_App".
    apply T_App with T11...
  Case "T_Fst".
    apply T_Fst with T2...
  Case "T_Snd".
    apply T_Snd with T1...
  Case "T_Case".
    apply T_Case with T1 T2...
  Case "T_BindIO".
    apply T_BindIO with T1...
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
    SCase "inr". inversion HT1; subst...
  Case "T_Fix".
    inversion HE; subst...
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
  


End SmtenProp.
