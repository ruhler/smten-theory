
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

End SmtenS.

