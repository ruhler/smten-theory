
Require Export Smten.
Require Export SmtenProp.
Require Export SmtenS.

Module SmtenIO.
Import Smten.Smten.
Import SmtenProp.SmtenProp.
Import SmtenS.SmtenS.

Inductive valueIO : tm -> Prop :=
  | vIO_return : forall t, valueIO (treturnIO t)
  .

Hint Constructors valueIO.


Reserved Notation "t1 '=IO=>' t2" (at level 40).

Inductive stepIO : tm -> tm -> Prop :=
  | STIO_Pure : forall t t',
      t ==> t' ->
      t =IO=> t'
  | STIO_BindReturn : forall t1 t2,
      tbindIO (treturnIO t1) t2 =IO=> tapp t2 t1
  | STIO_Bind : forall t1 t1' t2,
      t1 =IO=> t1' ->
      tbindIO t1 t2 =IO=> tbindIO t1' t2 
  | STIO_SearchEmpty : forall T,
      tsearchIO (temptyS T) =IO=> treturnIO (tnothing T)
  | STIO_SearchSingle : forall t,
      tsearchIO (tsingleS t) =IO=> treturnIO (tjust t)
  | STIO_Search : forall t t',
      t =S=> t' ->
      tsearchIO t =IO=> tsearchIO t'

where "t1 '=IO=>' t2" := (stepIO t1 t2).

Tactic Notation "stepIO_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STIO_Pure" | Case_aux c "STIO_BindReturn"
  | Case_aux c "STIO_Bind" | Case_aux c "STIO_SearchEmpty"
  | Case_aux c "STIO_SearchSingle" | Case_aux c "STIO_Search"
  ].

Hint Constructors stepIO.

Notation multistepIO := (multi stepIO).
Notation "t1 '=IO=>*' t2" := (multistepIO t1 t2) (at level 40).

Theorem progressIO : forall t T,
    empty |- t \in T ->
    (exists T1 : ty, T = TIO T1) ->
    valueIO t \/ exists t', t =IO=> t'.

Proof with eauto.
  intros t T Ht HIOt.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var". inversion H.
  Case "T_Abs". inversion HIOt. inversion H.
  Case "T_App". 
     (* progress says either tapp is a value or steps *)
     destruct (progress (tapp t1 t2) T12)...
     SCase "tapp is a value". inversion H.
     SCase "tapp steps". right. destruct H as [t3]...
  Case "T_Unit". inversion HIOt. inversion H.
  Case "T_Pair". inversion HIOt. inversion H.
  Case "T_Fst". 
     destruct(progress (tfst t) T1)...
     SCase "tfst is a value". inversion H.
     SCase "tfst steps". right. destruct H as [t2]...
  Case "T_Snd". 
     destruct (progress (tsnd t) T2)...
     SCase "tsnd is a value". inversion H.
     SCase "tsnd steps". right. destruct H as [t2]...
  Case "T_Inl". inversion HIOt. inversion H.
  Case "T_Inr". inversion HIOt. inversion H.
  Case "T_Case".
     destruct (progress (tcase t1 t2 t3) T3)...
     SCase "tcase is a value". inversion H.
     SCase "tcase steps". right. destruct H as [t4]...
  Case "T_BindIO".
     right. destruct IHHt1...
     SCase "t1 is a valueIO". inversion H...
     SCase "t1 is tbindIO". destruct H as [t3]...
  Case "T_SearchIO".
     right. destruct (progressS t (TS T))...
     SCase "t is a valueS".
       inversion H.
       SSCase "t is zeroS".
         exists (treturnIO (tnothing T0)). apply STIO_SearchEmpty.
       SSCase "t is returnS".
         exists (treturnIO (tjust t0)). apply STIO_SearchSingle.
     SCase "t steps".
       inversion H as [t'].
       exists (tsearchIO t'). apply STIO_Search. assumption.
  Case "T_EmptyS". inversion HIOt. inversion H.
  Case "T_SingleS". inversion HIOt. inversion H.
  Case "T_UnionS". inversion HIOt. inversion H.  
  Case "T_MapS". inversion HIOt. inversion H.
  Case "T_JoinS". inversion HIOt. inversion H.
Qed.

Theorem preservationIO : forall t t' T,
     empty |- t \in T ->
     t =IO=> t' ->
     empty |- t' \in T.

Proof with eauto.
   intros t t' T HT Hstep.
   generalize dependent T.
   stepIO_cases (induction Hstep) Case; intros Tx HT; subst...
   Case "STIO_Pure". apply preservation with t...
   Case "STIO_BindReturn". 
     inversion HT. inversion H2.
     apply T_App with T1...
   Case "STIO_Bind".
     inversion HT.
     apply T_BindIO with T1...
   Case "STIO_SearchEmpty".
     inversion HT.
     apply T_ReturnIO.
     inversion H1.
     apply T_Inl.
     apply T_Unit.
   Case "STIO_SearchSingle".
     inversion HT.
     apply T_ReturnIO.
     apply T_Inr.
     inversion H1. assumption.
   Case "STIO_Search".
     inversion HT.
     apply T_SearchIO.
     apply preservationS with t...
Qed.

Definition stuckIO (t:tm) : Prop :=
  (normal_form stepIO) t /\ ~ valueIO t.

Corollary soundnessIO : forall t t' T,
  empty |- t \in T -> 
  (exists T1, T = TIO T1) ->
  t =IO=>* t' ->
  ~(stuckIO t').
Proof.
  intros t t' T Hhas_type Hio Hmulti. unfold stuckIO.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti. apply Hnot_val. 
   destruct (progressIO x0 T).
   apply Hhas_type. apply Hio. apply H.
   contradiction.

   apply IHHmulti.
   apply (preservationIO x0 y0). apply Hhas_type. apply H.
   apply Hnf. apply Hnot_val.
Qed.


End SmtenIO.

