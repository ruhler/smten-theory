
Require Export Types.

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
  | treturnIO : tm -> tm            (* return_IO t *)
  | tbindIO : tm -> tm -> tm        (* bind_IO t1 t2 *)
  | trunIO : tm -> tm               (* run_IO t *)
  | treturnS : tm -> tm             (* return_S t *)
  | tbindS : tm -> tm -> tm         (* bind_S t1 t2 *)
  | tzeroS : ty -> tm               (* mzero *)
  | tplusS : tm -> tm -> tm         (* mplus *)
  .

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tunit" 
  | Case_aux c "tpair" | Case_aux c "tfst" | Case_aux c "tsnd" 
  | Case_aux c "tinl" | Case_aux c "tinr" | Case_aux c "tcase"
  | Case_aux c "tfix" 
  | Case_aux c "treturnIO" | Case_aux c "tbindIO"  | Case_aux c "trunIO"
  | Case_aux c "treturnS" | Case_aux c "tbindS"
  | Case_aux c "tzeroS" | Case_aux c "tplusS" ].

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
  | v_runIO : forall t, value (trunIO t)
  | v_returnS : forall t, value (treturnS t)
  | v_bindS : forall t1 t2, value (tbindS t1 t2)
  | v_zeroS : forall T, value (tzeroS T)
  | v_plusS : forall t1 t2, value (tplusS t1 t2)
  .

Tactic Notation "v_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "v_abs" | Case_aux c "v_unit"
  | Case_aux c "v_pair"
  | Case_aux c "v_inl" | Case_aux c "v_inr" 
  | Case_aux c "v_returnIO" | Case_aux c "v_bindIO" | Case_aux c "v_runIO"
  | Case_aux c "v_returnS" | Case_aux c "v_bindS"
  | Case_aux c "v_zeroS" | Case_aux c "v_plusS"
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
  | trunIO t1 => trunIO ([x:=s] t1)
  | treturnS t1 => treturnS ([x:=s] t1)
  | tbindS t1 t2 => tbindS ([x:=s] t1) ([x:=s] t2)
  | tzeroS T => tzeroS T
  | tplusS t1 t2 => tplusS ([x:=s] t1) ([x:=s] t2)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t1 t2,
         (tapp (tabs x T t1) t2) ==> [x:=t2]t1
  | ST_App1 : forall t1 t1' t2,
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
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
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
  | T_RunIO : forall Gamma t T,
       Gamma |- t \in (TS T) ->
       Gamma |- trunIO t \in (TIO (TMaybe T))
  | T_ReturnS : forall Gamma t T,
       Gamma |- t \in T ->
       Gamma |- treturnS t \in (TS T)
  | T_BindS : forall Gamma t1 t2 T1 T2,
       Gamma |- t1 \in (TS T1) ->
       Gamma |- t2 \in (TArrow T1 (TS T2)) ->
       Gamma |- tbindS t1 t2 \in (TS T2)
  | T_ZeroS : forall Gamma T,
       Gamma |- tzeroS T \in (TS T)
  | T_PlusS : forall Gamma t1 t2 T,
       Gamma |- t1 \in (TS T) ->
       Gamma |- t2 \in (TS T) ->
       Gamma |- tplusS t1 t2 \in (TS T)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_Unit" 
  | Case_aux c "T_Pair" | Case_aux c "T_Fst" | Case_aux c "T_Snd" 
  | Case_aux c "T_Inl" | Case_aux c "T_Inr" | Case_aux c "T_Case" 
  | Case_aux c "T_Fix"
  | Case_aux c "T_ReturnIO" | Case_aux c "T_BindIO" | Case_aux c "T_RunIO"
  | Case_aux c "T_ReturnS" | Case_aux c "T_BindS" 
  | Case_aux c "T_ZeroS" | Case_aux c "T_PlusS" ].

Hint Constructors has_type.

End Smten.

