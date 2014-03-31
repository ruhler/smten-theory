
Require Export SfLib.

Module Smten.

Inductive ty : Type := 
  | TArrow : ty -> ty -> ty         (* T -> T *)
  | TUnit  : ty                     (* Unit *)
  | TProd  : ty -> ty -> ty         (* T1 * T2 *)
  | TSum   : ty -> ty -> ty         (* T1 + T2 *)
  | TIO    : ty -> ty               (* IO T *)
  | TS     : ty -> ty               (* S T *)
  .

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TArrow"
  | Case_aux c "TUnit" | Case_aux c "TProd" | Case_aux c "TSum" 
  | Case_aux c "TIO" | Case_aux c "TS" ].

Inductive tm : Type :=
  | tvar : id -> tm                 (* x *)
  | tapp : tm -> tm -> tm           (* t1 t2 *)
  | tabs : id -> ty -> tm -> tm     (* \x:T.t *)
  | tunit : tm                      (* unit *)
  | tpair : tm -> tm -> tm          (* (t1, t2) *)
  | tfst : tm -> tm                 (* fst t1 *)
  | tsnd : tm -> tm                 (* snd t1 *)
  | tinl : ty -> tm -> tm           (* inl T t *)
  | tinr : ty -> tm -> tm           (* inr T t *)
  | tcase : tm -> tm -> tm -> tm    (* case t0 t1 t2 *)
  | tfix : tm -> tm                 (* fix t *)

    (* IO space primitives *)
  | treturnIO : tm -> tm            (* return_IO t *)
  | tbindIO : tm -> tm -> tm        (* bind_IO t1 t2 *)
  | tsearchIO : tm -> tm            (* search_IO t *)

    (* Search space primitives *)
  | temptyS : ty -> tm              (* empty *)
  | tsingleS : tm -> tm             (* single t *)
  | tunionS : tm -> tm -> tm        (* union t1 t2 *)
  | tmapS : tm -> tm -> tm          (* map t1 t2 *)
  | tjoinS : tm -> tm               (* join t *)
  .

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tunit" 
  | Case_aux c "tpair" | Case_aux c "tfst" | Case_aux c "tsnd" 
  | Case_aux c "tinl" | Case_aux c "tinr" | Case_aux c "tcase"
  | Case_aux c "tfix" 
  | Case_aux c "treturnIO" | Case_aux c "tbindIO"  | Case_aux c "tsearchIO"
  | Case_aux c "temptyS" | Case_aux c "tsingleS" | Case_aux c "tunionS"
  | Case_aux c "tmapS" | Case_aux c "tjoinS" ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Notation "'TMaybe' T" := (TSum TUnit T) (at level 20).
Notation "'tnothing' T" := (tinl T tunit) (at level 20).
Notation "'tjust' t" := (tinr TUnit t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (tabs x T t)
  | v_unit : value tunit 
  | v_pair : forall t1 t2, value (tpair t1 t2)
  | v_inl : forall T t, value (tinl T t)
  | v_inr : forall T t, value (tinr T t)
  | v_returnIO : forall t, value (treturnIO t)
  | v_bindIO : forall t1 t2, value (tbindIO t1 t2)
  | v_searchIO : forall t, value (tsearchIO t)
  | v_emptyS : forall T, value (temptyS T)
  | v_singleS : forall t, value (tsingleS t)
  | v_unionS : forall t1 t2, value (tunionS t1 t2)
  | v_mapS : forall t1 t2, value (tmapS t1 t2)
  | v_joinS : forall t, value (tjoinS t)
  .

Tactic Notation "v_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "v_abs" | Case_aux c "v_unit"
  | Case_aux c "v_pair"
  | Case_aux c "v_inl" | Case_aux c "v_inr" 
  | Case_aux c "v_returnIO" | Case_aux c "v_bindIO" | Case_aux c "v_searchIO"
  | Case_aux c "v_emptyS" | Case_aux c "v_singleS" | Case_aux c "v_unionS"
  | Case_aux c "v_mapS" | Case_aux c "v_joinS"
  ].

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => if eq_id_dec x x' then s else t
  | tabs x' T t1 => tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => tapp ([x:=s] t1) ([x:=s] t2)
  | tunit => tunit
  | tpair t1 t2 => tpair ([x:=s] t1) ([x:=s] t2)
  | tfst t1 => tfst ([x:=s] t1)
  | tsnd t1 => tsnd ([x:=s] t1)
  | tinl T t1 => tinl T ([x:=s] t1)
  | tinr T t1 => tinr T ([x:=s] t1)
  | tcase t1 t2 t3 => tcase ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | tfix t1 => tfix ([x:=s] t1)
  | treturnIO t1 => treturnIO ([x:=s] t1)
  | tbindIO t1 t2 => tbindIO ([x:=s] t1) ([x:=s] t2)
  | tsearchIO t1 => tsearchIO ([x:=s] t1)
  | temptyS T => temptyS T
  | tsingleS t1 => tsingleS ([x:=s] t1)
  | tunionS t1 t2 => tunionS ([x:=s] t1) ([x:=s] t2)
  | tmapS t1 t2 => tmapS ([x:=s] t1) ([x:=s] t2)
  | tjoinS t1 => tjoinS ([x:=s] t1)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t1 t2,
         (tapp (tabs x T t1) t2) ==> [x:=t2]t1
  | ST_App : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_FstPair : forall t1 t2,
      (tfst (tpair t1 t2)) ==> t1
  | ST_Fst : forall t t',
      t ==> t' ->
      tfst t ==> tfst t'
  | ST_SndPair : forall t1 t2,
      (tsnd (tpair t1 t2)) ==> t2
  | ST_Snd : forall t t',
      t ==> t' ->
      tsnd t ==> tsnd t'
  | ST_CaseInl : forall T t1 t2 t3,
      (tcase (tinl T t1) t2 t3) ==> (tapp t2 t1)
  | ST_CaseInr : forall T t1 t2 t3,
      (tcase (tinr T t1) t2 t3) ==> (tapp t3 t1)
  | ST_Case : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tcase t1 t2 t3 ==> tcase t1' t2 t3
  | ST_Fix : forall t,
      tfix t ==> tapp t (tfix t)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App" 
  | Case_aux c "ST_FstPair" | Case_aux c "ST_Fst"
  | Case_aux c "ST_SndPair" | Case_aux c "ST_Snd"
  | Case_aux c "ST_CaseInl" | Case_aux c "ST_CaseInr" | Case_aux c "ST_Case" 
  | Case_aux c "ST_Fix" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_Unit : forall Gamma,
       Gamma |- tunit \in TUnit
  | T_Pair : forall Gamma t1 t2 T1 T2,
       Gamma |- t1 \in T1 ->
       Gamma |- t2 \in T2 ->
       Gamma |- (tpair t1 t2) \in (TProd T1 T2)
  | T_Fst : forall Gamma t T1 T2,
       Gamma |- t \in (TProd T1 T2) ->
       Gamma |- (tfst t) \in T1
  | T_Snd : forall Gamma t T1 T2,
       Gamma |- t \in (TProd T1 T2) ->
       Gamma |- (tsnd t) \in T2
  | T_Inl : forall Gamma t T1 T2,
       Gamma |- t \in T1 ->
       Gamma |- (tinl T2 t) \in (TSum T1 T2)
  | T_Inr : forall Gamma t T1 T2,
       Gamma |- t \in T2 ->
       Gamma |- (tinr T1 t) \in (TSum T1 T2)
  | T_Case : forall Gamma t1 t2 t3 T1 T2 T3,
       Gamma |- t1 \in (TSum T1 T2) ->
       Gamma |- t2 \in (TArrow T1 T3) ->
       Gamma |- t3 \in (TArrow T2 T3) ->
       Gamma |- (tcase t1 t2 t3) \in T3
  | T_Fix : forall Gamma t T,
       Gamma |- t \in (TArrow T T) ->
       Gamma |- tfix t \in T
  | T_ReturnIO : forall Gamma t T,
       Gamma |- t \in T ->
       Gamma |- treturnIO t \in (TIO T)
  | T_BindIO : forall Gamma t1 t2 T1 T2,
       Gamma |- t1 \in (TIO T1) ->
       Gamma |- t2 \in (TArrow T1 (TIO T2)) ->
       Gamma |- tbindIO t1 t2 \in (TIO T2)
  | T_SearchIO : forall Gamma t T,
       Gamma |- t \in (TS T) ->
       Gamma |- tsearchIO t \in (TIO (TMaybe T))
  | T_EmptyS : forall Gamma T,
       Gamma |- temptyS T \in (TS T)
  | T_SingleS : forall Gamma t T,
       Gamma |- t \in T ->
       Gamma |- tsingleS t \in (TS T)
  | T_UnionS : forall Gamma t1 t2 T,
       Gamma |- t1 \in (TS T) ->
       Gamma |- t2 \in (TS T) ->
       Gamma |- tunionS t1 t2 \in (TS T)
  | T_MapS : forall Gamma t1 t2 T1 T2,
       Gamma |- t1 \in (TArrow T1 T2) ->
       Gamma |- t2 \in (TS T1) ->
       Gamma |- tmapS t1 t2 \in (TS T2)
  | T_JoinS : forall Gamma t T,
       Gamma |- t \in (TS (TS T)) ->
       Gamma |- tjoinS t \in (TS T)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_Unit" 
  | Case_aux c "T_Pair" | Case_aux c "T_Fst" | Case_aux c "T_Snd" 
  | Case_aux c "T_Inl" | Case_aux c "T_Inr" | Case_aux c "T_Case" 
  | Case_aux c "T_Fix"
  | Case_aux c "T_ReturnIO" | Case_aux c "T_BindIO" | Case_aux c "T_SearchIO"
  | Case_aux c "T_EmptyS" | Case_aux c "T_SingleS" | Case_aux c "T_UnionS"
  | Case_aux c "T_MapS" | Case_aux c "T_JoinS" ].

Hint Constructors has_type.

End Smten.

