
Require Export Smten.
Require Export SmtenProp.

Module SmtenIO.
Import Smten.Smten.
Import SmtenProp.SmtenProp.

Inductive valueio : tm -> Prop :=
  | vio_return : forall t, valueio (treturnio t)
  .

Hint Constructors valueio.


Reserved Notation "t1 '=IO=>' t2" (at level 40).

Inductive stepio : tm -> tm -> Prop :=
  | STIO_Pure : forall t t',
      t ==> t' ->
      t =IO=> t'
  | STIO_BindReturn : forall t1 t2,
      tbindio (treturnio t1) t2 =IO=> tapp t2 t1
  | STIO_Bind : forall t1 t1' t2,
      t1 =IO=> t1' ->
      tbindio t1 t2 =IO=> tbindio t1' t2 

where "t1 '=IO=>' t2" := (stepio t1 t2).

Tactic Notation "stepio_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STIO_Pure" | Case_aux c "STIO_BindReturn"
  | Case_aux c "STIO_Bind" ].

Hint Constructors stepio.

Notation multistepio := (multi stepio).
Notation "t1 '=IO=>*' t2" := (multistepio t1 t2) (at level 40).


Theorem progressio : forall t T,
    empty |- t \in T ->
    (exists T1 : ty, T = TIO T1) ->
    valueio t \/ exists t', t =IO=> t'.

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
     SCase "t1 is a valueio". inversion H...
     SCase "t1 is tbindio". destruct H as [t3]...
Qed.

End SmtenIO.

