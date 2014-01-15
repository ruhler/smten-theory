
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

Theorem progressS1 : forall t T,
    empty |- t \in T ->
    (exists T1 : ty, T = TS T1) ->
    valueS1 t \/ exists t', t =S1=> t'.

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
  Case "T_RunIO". inversion HSt. inversion H.
  Case "T_BindS".
     right. destruct IHHt1...
     SCase "t1 is a valueS1". inversion H.
      SSCase "t1 is returnS t". 
           exists (tapp t2 t). apply STS1_BindReturn.
      SSCase "t1 is zeroS".
           rewrite <- H0 in Ht1.
           inversion Ht1.
           exists (tzeroS T2).
           apply STS1_BindZero...      
      SSCase "t1 is plusS".
           exists (tplusS (tbindS t0 t2) (tbindS t3 t2)). apply STS1_BindPlus.
     SCase "t1 steps". inversion H as [t3]...
Qed.

Theorem preservationS1 : forall t t' T,
     empty |- t \in T ->
     t =S1=> t' ->
     empty |- t' \in T.

Proof with eauto.
   intros t t' T HT Hstep.
   generalize dependent T.
   stepS1_cases (induction Hstep) Case; intros T HT; subst...
   Case "STS1_Pure".
     apply preservation with t...
   Case "STS1_BindReturn".
     inversion HT. inversion H2.
     apply T_App with T1...
   Case "STS1_BindZero".
     inversion HT.
     assert (TArrow T1 (TS T2) = TArrow T0 (TS T3)).
     apply unique_typing with empty t...
     injection H6.
     intros .
     rewrite H7.
     apply T_ZeroS.
   Case "STS1_BindPlus".
     inversion HT. inversion H2.
     apply T_PlusS.
     apply T_BindS with T1...
     apply T_BindS with T1...
   Case "STS1_Bind".
     inversion HT.
     apply T_BindS with T1...
Qed.

Definition stuckS1 (t:tm) : Prop :=
  (normal_form stepS1) t /\ ~ valueS1 t.

Corollary soundnessS1 : forall t t' T,
  empty |- t \in T -> 
  (exists T1, T = TS T1) ->
  t =S1=>* t' ->
  ~(stuckS1 t').
Proof.
  intros t t' T Hhas_type Hio Hmulti. unfold stuckS1.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti. apply Hnot_val. 
   destruct (progressS1 x0 T).
   apply Hhas_type. apply Hio. apply H.
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
  Case "trunIO". sts1_pure (trunIO t) T.
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

