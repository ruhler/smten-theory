
Require Export Smten.
Require Export SmtenProp.

Module SmtenS1.
Import Smten.Smten.
Import SmtenProp.SmtenProp.

(* S1 steps get rid of bindS *)

Inductive valueS1 : tm -> Prop :=
  | vS1_return : forall t, valueS1 (treturnS t)
  | vS1_zero : forall T, valueS1 (tzeroS T)
  | vS1_plus : forall t1 t2, valueS1 (tplusS t1 t2)
  .

Hint Constructors valueS1.

Reserved Notation "t1 '=S1=>' t2" (at level 40).

Inductive stepS1 : tm -> tm -> Prop :=
  | STS1_Pure : forall t t',
      t ==> t' ->
      t =S1=> t'
  | STS1_BindReturn : forall t1 t2,
      tbindS (treturnS t1) t2 =S1=> tapp t2 t1
  | STS1_BindZero : forall T1 T2 t,
      empty |- t \in TArrow T1 (TS T2) ->
      tbindS (tzeroS T1) t =S1=> tzeroS T2
  | STS1_BindPlus : forall t1 t2 t3,
      tbindS (tplusS t1 t2) t3 =S1=> tplusS (tbindS t1 t3) (tbindS t2 t3)
  | STS1_Bind : forall t1 t1' t2,
      t1 =S1=> t1' ->
      tbindS t1 t2 =S1=> tbindS t1' t2 

where "t1 '=S1=>' t2" := (stepS1 t1 t2).

Tactic Notation "stepS1_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STS1_Pure" | Case_aux c "STS1_BindReturn"
  | Case_aux c "STS1_BindZero" | Case_aux c "STS1_BindPlus"
  | Case_aux c "STS1_Bind" ].

Hint Constructors stepS1.

Notation multistepS1 := (multi stepS1).
Notation "t1 '=S1=>*' t2" := (multistepS1 t1 t2) (at level 40).

Lemma pure_stepsS1 : forall t T,
    empty |- t \in T ->
    ~ (value t) ->
    exists t', t =S1=> t'.
Proof.
  intros t T HT Hnv.
  destruct (progress t T HT).
  Case "t is a value". contradiction.
  Case "t pure steps".
    destruct H as [t'].
    exists t'.
    apply STS1_Pure ; assumption.
Qed.

Theorem progressS1 : forall t T,
    empty |- t \in T ->
    (exists T1 : ty, T = TS T1) ->
    valueS1 t \/ exists t', t =S1=> t'.

Proof with eauto.
  intros t T Ht HSt.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case ; subst Gamma.
  Ltac is_valueS1 xx := left ; apply xx.
  Ltac not_type_S HSt := 
     (* Contradiction: The type of t is not of the form TS T *)
     destruct HSt ; discriminate H.
  Ltac pure_progress t T HT :=
     (* The term pure steps, so it s1-steps *)
     assert (Hnvalue : ~ (value t)) ;
     [ unfold not ; intro Hvalue ; inversion Hvalue 
     | right ; apply (pure_stepsS1 t T HT Hnvalue)].
  Case "T_Var". inversion H. (* var not well typed in empty context *)
  Case "T_Abs". not_type_S HSt.
  Case "T_App". pure_progress (tapp t1 t2) T12 (T_App T11 T12 empty t1 t2 Ht1 Ht2).
  Case "T_Unit". not_type_S HSt.
  Case "T_Pair". not_type_S HSt.
  Case "T_Fst". pure_progress (tfst t) T1 (T_Fst empty t T1 T2 Ht). 
  Case "T_Snd". pure_progress (tsnd t) T2 (T_Snd empty t T1 T2 Ht).
  Case "T_Inl". not_type_S HSt.
  Case "T_Inr". not_type_S HSt.
  Case "T_Case". pure_progress (tcase t1 t2 t3) T3 (T_Case empty t1 t2 t3 T1 T2 T3 Ht1 Ht2 Ht3).
  Case "T_Fix". pure_progress (tfix t) T (T_Fix empty t T Ht).
  Case "T_ReturnIO". not_type_S HSt.
  Case "T_BindIO". not_type_S HSt.
  Case "T_SearchIO". not_type_S HSt.
  Case "T_ReturnS". is_valueS1 vS1_return.
  Case "T_BindS".
     (* bindS t1 t2:
        by induction, t1 is either an s1-value, or s1-steps.
          s1-value returnS: BindReturn applies
          s1-value zero: BindZero applies
          s1-value plus: BindPlus applies
          s1-steps: Bind applies
     *)
     right.
     destruct (IHHt1 (eq_refl empty) (ex_intro (fun T2 => TS T1 = TS T2) T1 eq_refl)).
     SCase "t1 is a valueS1". inversion H ; subst.
      SSCase "t1 is returnS t". 
         exists (tapp t2 t). apply STS1_BindReturn.
      SSCase "t1 is zeroS".
         inversion Ht1.
         exists (tzeroS T2). apply STS1_BindZero ; assumption.
      SSCase "t1 is plusS".
         exists (tplusS (tbindS t0 t2) (tbindS t3 t2)). apply STS1_BindPlus.
     SCase "t1 steps".
         destruct H as [t1'].
         exists (tbindS t1' t2).
         apply STS1_Bind ; assumption.
  Case "T_ZeroS". is_valueS1 vS1_zero.
  Case "T_PlusS". is_valueS1 vS1_plus.
Qed.

Theorem preservationS1 : forall t t' T,
     empty |- t \in T ->
     t =S1=> t' ->
     empty |- t' \in T.

Proof.
   intros t t' T HT Hstep.
   generalize dependent T.
   stepS1_cases (induction Hstep) Case; intros T HT.
   Case "STS1_Pure".
     (* preservationS1 comes because we have pure preservation *)
     apply preservation with t ; assumption.
   Case "STS1_BindReturn".
     (* Given HT, tapp t2 t1 must have type T by T_App *)
     inversion HT ; subst ; inversion H2 ; subst.
     apply T_App with T1 ; assumption.
   Case "STS1_BindZero".
     (* Types T2 and T are equal because typing is unique. *)
     inversion HT ; subst.
     assert (Htarreq : TArrow T1 (TS T2) = TArrow T0 (TS T3)).
     apply unique_typing with empty t ; assumption.
     injection Htarreq.
     intros ; subst.
     apply T_ZeroS.
   Case "STS1_BindPlus".
     inversion HT ; subst ; inversion H2 ; subst.
     apply T_PlusS ; apply T_BindS with T1 ; assumption.
   Case "STS1_Bind".
     (* by induction on t1 preserving typing *)
     inversion HT ; subst.
     apply T_BindS with T1.
     apply IHHstep ; assumption.
     assumption.
Qed.

Definition stuckS1 (t:tm) : Prop :=
  (normal_form stepS1) t /\ ~ valueS1 t.

Corollary soundnessS1 : forall t t' T,
  empty |- t \in T -> 
  (exists T1, T = TS T1) ->
  t =S1=>* t' ->
  ~(stuckS1 t').
Proof.
  intros t t' T Hhas_type Hs Hmulti. unfold stuckS1.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti. apply Hnot_val. 
   destruct (progressS1 x0 T).
   apply Hhas_type. apply Hs. apply H.
   contradiction.

   apply IHHmulti.
   apply (preservationS1 x0 y0). apply Hhas_type. apply H.
   apply Hnf. apply Hnot_val.
Qed.

Theorem stepS1_deterministic : forall t t1 t2 T,
   empty |- t \in T ->
   t =S1=> t1 ->
   t =S1=> t2 ->
   t1 = t2
   .

(* sts1_pure: A tactic to handle the case where determinism of stepS1 comes
   directly from determinism of step. *)
Ltac sts1_pure tx T := 
  inversion Hstep1 ;
  inversion Hstep2 ;
  apply step_deterministic with tx T;
  repeat assumption.

Proof.
  intro t.
  t_cases (induction t) Case; intros tx ty T HT Hstep1 Hstep2.
  Case "tvar". sts1_pure (tvar i) T.
  Case "tapp". sts1_pure (tapp t1 t2) T.
  Case "tabs". sts1_pure (tabs i t t0) T.
  Case "tunit". sts1_pure tunit T.
  Case "tpair". sts1_pure (tpair t1 t2) T.
  Case "tfst". sts1_pure (tfst t) T.
  Case "tsnd". sts1_pure (tsnd t) T.
  Case "tinl". sts1_pure (tinl t t0) T.
  Case "tinr". sts1_pure (tinr t t0) T.
  Case "tcase". sts1_pure (tcase t1 t2 t3) T.
  Case "tfix". sts1_pure (tfix t) T.
  Case "treturnIO". sts1_pure (treturnIO t) T.
  Case "tbindIO". sts1_pure (tbindIO t1 t2) T.
  Case "tsearchIO". sts1_pure (tsearchIO t) T.
  Case "treturnS". sts1_pure (treturnS t) T.
  Case "tbindS". 
    inversion Hstep1.
    SCase "pure step to tx".
       inversion Hstep2.
       SSCase "pure step to ty".
           apply step_deterministic with (tbindS t1 t2) T.
           assumption. assumption. assumption.
       SSCase "BindReturn to ty". inversion H.
       SSCase "BindZero to ty". inversion H.
       SSCase "BindPlus to ty". inversion H.
       SSCase "Bind to ty". inversion H.
    SCase "BindReturn to tx".
       rewrite <- H0 in Hstep2.
       inversion Hstep2.
       SSCase "pure step to ty". inversion H.
       SSCase "BindReturn to ty". reflexivity.
       SSCase "Bind to ty". inversion H5. inversion H6.
    SCase "BindZero to tx".
       rewrite <- H in Hstep2.
       inversion Hstep2.
       SSCase "pure step to ty". inversion H3.
       SSCase "BindZero to ty".
         assert (TArrow T1 (TS T2) = TArrow T1 (TS T3)).
         apply unique_typing with empty t2.
         assumption. assumption.
         injection H7. intro Hteq. rewrite Hteq. reflexivity.
       SSCase "Bind to ty". inversion H6. inversion H7.
    SCase "BindPlus to tx".
       rewrite <- H0 in Hstep2.
       inversion Hstep2.
       SSCase "pure to ty". inversion H.
       SSCase "BindPlus to ty". reflexivity.
       SSCase "Bind to ty". inversion H5. inversion H6.
    SCase "Bind to tx".
       inversion Hstep2.
       SSCase "pure to ty". inversion H3.
       SSCase "BindReturn to ty".
         rewrite <- H4 in H2.
         inversion H2. inversion H6.
       SSCase "BindZero to ty".
         rewrite <- H3 in H2.
         inversion H2. inversion H7.
       SSCase "BindPlus to ty".
         rewrite <- H4 in H2.
         inversion H2. inversion H6.
       SSCase "Bind to ty".
         f_equal.
         inversion HT.
         apply IHt1 with (TS T1).
         assumption. assumption. assumption.
  Case "tzeroS". inversion Hstep1. inversion H.
  Case "tplusS". inversion Hstep1. inversion H.
Qed.

End SmtenS1.

