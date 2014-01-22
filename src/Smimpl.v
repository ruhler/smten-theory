
Require Export SfLib.
Require Export Sat.

Module Smimpl.
Import Sat.Sat.

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
  | tvar : id -> tm                     (* x *)
  | tapp : tm -> tm -> tm               (* t1 t2 *)
  | tabs : id -> ty -> tm -> tm         (* \x:T.t *)
  | tunit : tm                          (* unit *)
  | tpair : tm -> tm -> tm              (* (t1, t2) *)
  | tfst : tm -> tm                     (* fst t1 *)
  | tsnd : tm -> tm                     (* snd t1 *)
  | tinl : ty -> tm -> tm               (* inl T t *)
  | tinr : ty -> tm -> tm               (* inr T t *)
  | tsum : formula -> tm -> tm -> tm    (* if p then (inl t1) else (inr t2) *)
  | tcase : tm -> tm -> tm -> tm        (* case t0 t1 t2 *)
  | tfix : tm -> tm                     (* fix t *)
  | tite : formula -> tm -> tm -> tm    (* if p then t1 else t2 *)
  | treturnIO : tm -> tm                (* return_IO t *)
  | tbindIO : tm -> tm -> tm            (* bind_IO t1 t2 *)
  | trunIO : tm -> tm                   (* run_IO t *)
  | titeIO : formula -> tm -> tm -> tm  (* if p then t1 else t2 *)
  | treturnS : tm -> tm                 (* return_S t *)
  | tbindS : tm -> tm -> tm             (* bind_S t1 t2 *)
  | tzeroS : ty -> tm                   (* mzero *)
  | tplusS : tm -> tm -> tm             (* mplus *)
  | tsetS : formula -> tm -> tm         (* if p then (returnS t) else zeroS *)
  | titeS : formula -> tm -> tm -> tm   (* if p then t1 else t2 *)
  .

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tunit" 
  | Case_aux c "tpair" | Case_aux c "tfst" | Case_aux c "tsnd" 
  | Case_aux c "tinl" | Case_aux c "tinr" | Case_aux c "tsum"
  | Case_aux c "tcase"
  | Case_aux c "tfix" | Case_aux c "tite"
  | Case_aux c "treturnIO" | Case_aux c "tbindIO"  | Case_aux c "trunIO"
  | Case_aux c "titeIO" 
  | Case_aux c "treturnS" | Case_aux c "tbindS"
  | Case_aux c "tzeroS" | Case_aux c "tplusS" 
  | Case_aux c "tsetS" | Case_aux c "titeS"
  ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Notation "'TMaybe' T" := (TSum TUnit T) (at level 20).
Notation "'tnothing' T" := (tinl T tunit) (at level 20).
Notation "'tjust' t" := (tinr TUnit t) (at level 20).
Notation "'terr' T" := (tfix (tabs x T (tvar x))) (at level 20).

Inductive svalue : tm -> Prop :=
  | sv_returnS : forall t, svalue (treturnS t)
  | sv_bindS : forall t1 t2, svalue (tbindS t1 t2)
  | sv_zeroS : forall T, svalue (tzeroS T)
  | sv_plusS : forall t1 t2, svalue (tplusS t1 t2)
  | sv_setS : forall p t, svalue (tsetS p t)
  | sv_iteS : forall p t1 t2, svalue (titeS p t1 t2)
  .

Tactic Notation "sv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "sv_returnS" | Case_aux c "sv_bindS"
  | Case_aux c "sv_zeroS" | Case_aux c "sv_plusS"
  | Case_aux c "sv_setS" | Case_aux c "sv_iteS"
  ].

Hint Constructors svalue.

Inductive iovalue : tm -> Prop :=
  | iov_returnIO : forall t, iovalue (treturnIO t)
  | iov_bindIO : forall t1 t2, iovalue (tbindIO t1 t2)
  | iov_runIO : forall t, iovalue (trunIO t)
  | iov_iteIO : forall p t1 t2, iovalue (titeIO p t1 t2)
  .

Tactic Notation "iov_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "iov_returnIO" | Case_aux c "iov_bindIO"
  | Case_aux c "sv_runIO" | Case_aux c "sv_iteIO"
  ].

Hint Constructors iovalue.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (tabs x T t)
  | v_unit : value tunit 
  | v_pair : forall t1 t2, value (tpair t1 t2)
  | v_sum : forall p t1 t2, value (tsum p t1 t2)
  | v_IO : forall t, iovalue t -> value t
  | v_S : forall t, svalue t -> value t
  .

Tactic Notation "v_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "v_abs" | Case_aux c "v_unit"
  | Case_aux c "v_pair" | Case_aux c "v_sum"
  | Case_aux c "v_IO" | Case_aux c "v_S"
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
  | tsum p t1 t2 => tsum p ([x:=s] t1) ([x:=s] t2)
  | tcase t1 t2 t3 => tcase ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | tfix t1 => tfix ([x:=s] t1)
  | tite p t1 t2 => tite p ([x:=s] t1) ([x:=s] t2)
  | treturnIO t1 => treturnIO ([x:=s] t1)
  | tbindIO t1 t2 => tbindIO ([x:=s] t1) ([x:=s] t2)
  | trunIO t1 => trunIO ([x:=s] t1)
  | titeIO p t1 t2 => titeIO p ([x:=s] t1) ([x:=s] t2)
  | treturnS t1 => treturnS ([x:=s] t1)
  | tbindS t1 t2 => tbindS ([x:=s] t1) ([x:=s] t2)
  | tzeroS T => tzeroS T
  | tplusS t1 t2 => tplusS ([x:=s] t1) ([x:=s] t2)
  | tsetS p t1 => tsetS p ([x:=s] t1)
  | titeS p t1 t2 => titeS p ([x:=s] t1) ([x:=s] t2)
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
  | ST_Inl : forall T t,
      tinl T t ==> tsum ftrue t (terr T)
  | ST_Inr : forall T t,
      tinr T t ==> tsum ffalse (terr T) t
  | ST_CaseSum : forall p t1 t2 t3 t4,
      tcase (tsum p t1 t2) t3 t4 ==> tite p (tapp t3 t1) (tapp t4 t2)
  | ST_Case : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tcase t1 t2 t3 ==> tcase t1' t2 t3
  | ST_Fix : forall t,
      tfix t ==> tapp t (tfix t)
  | ST_Ite1 : forall p t1 t1' t2,
      t1 ==> t1' ->
      tite p t1 t2 ==> tite p t1' t2
  | ST_Ite2 : forall p t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tite p t1 t2 ==> tite p t1 t2'
  | ST_IteAbs : forall p x1 t1 x2 t2 T,
      tite p (tabs x1 T t1) (tabs x2 T t2) ==>
        tabs x T (tite p (tapp (tabs x1 T t1) (tvar x)) (tapp (tabs x2 T t2) (tvar x)))
  | ST_IteUnit : forall p,
      tite p tunit tunit ==> tunit
  | ST_ItePair : forall p t11 t12 t21 t22,
      tite p (tpair t11 t12) (tpair t21 t22) ==> 
        tpair (tite p t11 t21) (tite p t12 t22)
  | ST_IteSum : forall p p1 t11 t12 p2 t21 t22,
      tite p (tsum p1 t11 t12) (tsum p2 t21 t22) ==>
        tsum (fite p p1 p2) (tite p t11 t21) (tite p t12 t22)
  | ST_IteIO : forall p t1 t2,
      iovalue t1 ->
      iovalue t2 ->
      tite p t1 t2 ==> titeIO p t1 t2
  | ST_IteS : forall p t1 t2,
      svalue t1 ->
      svalue t2 ->
      tite p t1 t2 ==> titeS p t1 t2
      


where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_FstPair" | Case_aux c "ST_Fst"
  | Case_aux c "ST_SndPair" | Case_aux c "ST_Snd"
  | Case_aux c "ST_Inl" | Case_aux c "ST_Inr"
  | Case_aux c "ST_CaseSum" | Case_aux c "ST_Case" 
  | Case_aux c "ST_Fix" 
  | Case_aux c "ST_Ite1" | Case_aux c "ST_Ite2"
  | Case_aux c "ST_IteAbs" | Case_aux c "ST_IteUnit"
  | Case_aux c "ST_ItePair" | Case_aux c "ST_IteSum"
  | Case_aux c "ST_IteIO" | Case_aux c "St_IteS"
  ].

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
  | T_Sum : forall Gamma p t1 t2 T1 T2,
       Gamma |- t1 \in T1 ->
       Gamma |- t2 \in T2 ->
       Gamma |- (tsum p t1 t2) \in (TSum T1 T2)
  | T_Case : forall Gamma t1 t2 t3 T1 T2 T3,
       Gamma |- t1 \in (TSum T1 T2) ->
       Gamma |- t2 \in (TArrow T1 T3) ->
       Gamma |- t3 \in (TArrow T2 T3) ->
       Gamma |- (tcase t1 t2 t3) \in T3
  | T_Fix : forall Gamma t T,
       Gamma |- t \in (TArrow T T) ->
       Gamma |- tfix t \in T
  | T_Ite : forall Gamma p t1 t2 T,
       Gamma |- t1 \in T ->
       Gamma |- t2 \in T ->
       Gamma |- tite p t1 t2 \in T
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
  | T_IteIO : forall Gamma p t1 t2 T,
       Gamma |- t1 \in TIO T ->
       Gamma |- t2 \in TIO T ->
       Gamma |- titeIO p t1 t2 \in TIO T
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
  | T_SetS : forall Gamma p t T,
       Gamma |- t \in T ->
       Gamma |- tsetS p t \in TS T
  | T_IteS : forall Gamma p t1 t2 T,
       Gamma |- t1 \in TS T ->
       Gamma |- t2 \in TS T ->
       Gamma |- titeS p t1 t2 \in TS T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_Unit" 
  | Case_aux c "T_Pair" | Case_aux c "T_Fst" | Case_aux c "T_Snd" 
  | Case_aux c "T_Inl" | Case_aux c "T_Inr" | Case_aux c "T_Sum"
  | Case_aux c "T_Case" 
  | Case_aux c "T_Fix" | Case_aux c "T_Ite"
  | Case_aux c "T_ReturnIO" | Case_aux c "T_BindIO" | Case_aux c "T_RunIO"
  | Case_aux c "T_IteIO"
  | Case_aux c "T_ReturnS" | Case_aux c "T_BindS" 
  | Case_aux c "T_ZeroS" | Case_aux c "T_PlusS"
  | Case_aux c "T_SetS" | Case_aux c "T_IteS"
  ].

Hint Constructors has_type.

End Smimpl.

