
Require Export Smten.
Require Export SmtenProp.

Module SmtenS1.
Import Smten.Smten.
Import SmtenProp.SmtenProp.

(* S1 pulls empty, single, and union to the top *)

Inductive valueS1 : tm -> Prop :=
  | vS1_empty : forall T, valueS1 (temptyS T)
  | vS1_single : forall t, valueS1 (tsingleS t)
  | vS1_union : forall t1 t2, valueS1 (tunionS t1 t2)
  .

Hint Constructors valueS1.

Reserved Notation "t1 '=S1=>' t2" (at level 40).

Inductive stepS1 : tm -> tm -> Prop :=
  | STS1_Pure : forall t t',
      t ==> t' ->
      t =S1=> t'
  | STS1_MapEmpty : forall T1 T2 t,
      empty |- t \in TArrow T1 T2 ->
      tmapS t (temptyS T1) =S1=> temptyS T2
  | STS1_MapSingle : forall t1 t2,
      tmapS t1 (tsingleS t2) =S1=> tsingleS (tapp t1 t2)
  | STS1_MapUnion : forall t1 t2 t3,
      tmapS t1 (tunionS t2 t3) =S1=> tunionS (tmapS t1 t2) (tmapS t1 t3)
  | STS1_Map : forall t1 t2 t2',
      t2 =S1=> t2' ->
      tmapS t1 t2 =S1=> tmapS t1 t2'
  | STS1_JoinEmpty : forall T,
      tjoinS (temptyS (TS T)) =S1=> temptyS T
  | STS1_JoinSingle : forall t1,
      tjoinS (tsingleS t1) =S1=> t1
  | STS1_JoinUnion : forall t1 t2,
      tjoinS (tunionS t1 t2) =S1=> tunionS (tjoinS t1) (tjoinS t2)
  | STS1_Join : forall t1 t1',
      t1 =S1=> t1' ->
      tjoinS t1 =S1=> tjoinS t1'

where "t1 '=S1=>' t2" := (stepS1 t1 t2).

Tactic Notation "stepS1_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STS1_Pure"
  | Case_aux c "STS1_MapEmpty" | Case_aux c "STS1_MapSingle"
  | Case_aux c "STS1_MapUnion" | Case_aux c "STS1_Map"
  | Case_aux c "STS1_JoinEmpty" | Case_aux c "STS1_JoinSingle"
  | Case_aux c "STS1_JoinUnion" | Case_aux c "STS1_Join" ].

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
  Case "T_EmptyS". is_valueS1 vS1_empty.
  Case "T_SingleS". is_valueS1 vS1_single.
  Case "T_UnionS". is_valueS1 vS1_union.
  Case "T_MapS".
     (* mapS t1 t2:
        by induction, t1 is either an s1-value, or s1-steps.
          s1-value empty: MapEmpty applies
          s1-value single: MapSIngle applies
          s1-value union: MapUnion applies
          s1-steps: Map applies
     *)
     right.
     destruct (IHHt2 (eq_refl empty) (ex_intro (fun T2 => TS T1 = TS T2) T1 eq_refl)).
     SCase "t1 is a valueS1". inversion H ; subst.
      SSCase "t1 is emptyS".
         inversion Ht2. subst.
         exists (temptyS T2).
         exact (STS1_MapEmpty T1 T2 t1 Ht1).
      SSCase "t1 is singleS t". 
         exists (tsingleS (tapp t1 t)). apply STS1_MapSingle.
      SSCase "t1 is unionS".
         exists (tunionS (tmapS t1 t0) (tmapS t1 t3)). apply STS1_MapUnion.
     SCase "t1 steps".
         destruct H as [t2'].
         exists (tmapS t1 t2').
         apply STS1_Map ; assumption.
  Case "T_JoinS".
      (* joinS t1:
        by induction, t1 is either an s1-value, or s1-steps.
          s1-value empty: JoinZero applies
          s1-value single: JoinSingle applies
          s1-value union: JoinUnion applies
          s1-steps: Join applies
     *)
     right.
     destruct (IHHt (eq_refl empty) (ex_intro (fun T1 => TS (TS T) = TS T1) (TS T) eq_refl)).
     SCase "t1 is a valueS1". inversion H ; subst.
      SSCase "t1 is emptyS".
         inversion Ht.
         exists (temptyS T). apply STS1_JoinEmpty ; assumption.
      SSCase "t1 is singleS t". 
         exists (t0). apply STS1_JoinSingle.
      SSCase "t1 is unionS".
         exists (tunionS (tjoinS t1) (tjoinS t2)). apply STS1_JoinUnion.
     SCase "t1 steps".
         destruct H as [t1'].
         exists (tjoinS t1').
         apply STS1_Join ; assumption.
Qed.

Theorem preservationS1 : forall t t' T,
     empty |- t \in T ->
     t =S1=> t' ->
     empty |- t' \in T.

Proof.
   intros t t' T HT Hstep.
   generalize dependent T.
   stepS1_cases (induction Hstep) Case; intros TT HT.
   Case "STS1_Pure".
     (* preservationS1 comes because we have pure preservation *)
     apply preservation with t ; assumption.
   Case "STS1_MapEmpty".
     (* Types T2 and TT are equal because typing is unique. *)
     inversion HT ; subst.
     assert (Htarreq : TArrow T1 T2 = TArrow T0 T3).
     apply unique_typing with empty t ; assumption.
     injection Htarreq.
     intros ; subst.
     apply T_EmptyS.
   Case "STS1_MapSingle".
     (* Given HT, tsingle (tapp t2 t1) must have type TT by T_App *)
     inversion HT; subst ; inversion H4 ; subst.
     apply T_SingleS; apply T_App with T1 ; assumption.
   Case "STS1_MapUnion".
     inversion HT ; subst ; inversion H4 ; subst.
     apply T_UnionS ; apply T_MapS with T1 ; assumption.
   Case "STS1_Map".
     (* by induction on t1 preserving typing *)
     inversion HT ; subst.
     apply T_MapS with T1 . assumption.
     apply IHHstep ; assumption.
   Case "STS1_JoinEmpty".
     inversion HT ; subst ; inversion H1 ; subst.
     apply T_EmptyS.
   Case "STS1_JoinSingle".
     inversion HT ; subst.
     inversion H1 ; subst.
     assumption.
   Case "STS1_JoinUnion".
     inversion HT ; subst . inversion H1 ; subst.
     apply T_UnionS ; apply T_JoinS ; assumption.
   Case "STS1_Join".
     (* by induction on t1 preserving typing *)
     inversion HT ; subst.
     apply T_JoinS.
     apply IHHstep ; assumption.
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


Proof.
  intro t.
  t_cases (induction t) Case; intros tx ty T HT Hstep1 Hstep2.
  Ltac sts1_pure tx T := 
    (* Determinism of stepS1 comes directly from determinism of step, 
       because only sts1-pure applies .*)
    inversion Hstep1 ; inversion Hstep2 ;
    apply step_deterministic with tx T; assumption.
  Ltac doesnt_step_S1 := inversion Hstep1; inversion H.
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
  Case "treturnIO". doesnt_step_S1.
  Case "tbindIO". doesnt_step_S1.
  Case "tsearchIO". doesnt_step_S1.
  Case "temptyS". doesnt_step_S1.
  Case "tsingleS". doesnt_step_S1.
  Case "tunionS". doesnt_step_S1.
  Case "tmapS". 
    inversion Hstep1 ; subst.
    SCase "pure step to tx".
       (* there is no pure step from (mapS t1 t2), so this can't happen *)
       inversion H.
    SCase "MapEmpty to tx".
       inversion Hstep2.
       SSCase "pure step to ty". inversion H.
       SSCase "MapEmpty to ty".
         assert (Htarreq : TArrow T1 T2 = TArrow T1 T3).
         apply unique_typing with empty t1 ; assumption.
         injection Htarreq. intros ; subst ; reflexivity.
       SSCase "Map to ty". inversion H3. inversion H4.
    SCase "MapSingle to tx".
       inversion Hstep2.
       SSCase "pure step to ty". inversion H.
       SSCase "MapSingle to ty". reflexivity.
       SSCase "Map to ty".
         (* this would require singleS to s1-step, but it doesn't *)
         inversion H2. inversion H3.
    SCase "MapUnion to tx".
       inversion Hstep2.
       SSCase "pure to ty". inversion H.
       SSCase "MapUnion to ty". reflexivity.
       SSCase "Map to ty". inversion H2. inversion H3.
    SCase "Map to tx".
       inversion Hstep2 ; subst.
       SSCase "pure to ty". inversion H.
       SSCase "MapEmpty to ty".
         inversion H2. inversion H.
       SSCase "MapSingle to ty".
         inversion H2. inversion H.
       SSCase "MapUnion to ty".
         inversion H2. inversion H.
       SSCase "Map to ty".
         f_equal.
         inversion HT.
         apply IHt2 with (TS T1) ; assumption.
  Case "tjoinS". 
    inversion Hstep1 ; subst.
    SCase "pure step to tx".
       (* there is no pure step from (joinS t), so this can't happen *)
       inversion H.
    SCase "JoinEmpty to tx".
       inversion Hstep2.
       SSCase "pure step to ty". inversion H.
       SSCase "JoinEmpty to ty". reflexivity.
       SSCase "Join to ty". inversion H0. inversion H2.
    SCase "JoinSingle to tx".
       inversion Hstep2.
       SSCase "pure step to ty". inversion H.
       SSCase "JoinSingle to ty". reflexivity.
       SSCase "Join to ty".
         (* this would require singleS to s1-step, but it doesn't *)
         inversion H0. inversion H2.
    SCase "JoinUnion to tx".
       inversion Hstep2.
       SSCase "pure to ty". inversion H.
       SSCase "JoinUnion to ty". reflexivity.
       SSCase "Join to ty". inversion H0. inversion H2.
    SCase "Join to tx".
       inversion Hstep2 ; subst.
       SSCase "pure to ty". inversion H.
       SSCase "JoinEmpty to ty".
         inversion H0. inversion H.
       SSCase "JoinSingle to ty".
         inversion H0. inversion H.
       SSCase "JoinUnion to ty".
         inversion H0. inversion H.
       SSCase "Join to ty".
         f_equal.
         inversion HT.
         apply IHt with (TS (TS T0)) ; assumption.
Qed.

End SmtenS1.

