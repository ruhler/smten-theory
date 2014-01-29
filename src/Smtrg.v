
Require Export SfLib.
Require Export Sat.

Module Smtrg.
Import Sat.Sat.

Inductive ty : Type := 
  | TArrow : ty -> ty -> ty         (* T -> T *)
  | TUnit  : ty                     (* Unit *)
  | TProd  : ty -> ty -> ty         (* T1 * T2 *)
  | TFormula : ty                   (* Formula *)
  .

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TArrow"
  | Case_aux c "TUnit" | Case_aux c "TProd" | Case_aux c "TFormula" 
  ].

Inductive tm : Type :=
  | tvar : id -> tm                 (* x *)
  | tapp : tm -> tm -> tm           (* t1 t2 *)
  | tabs : id -> ty -> tm -> tm     (* \x:T.t *)
  | tunit : tm                      (* unit *)
  | tpair : tm -> tm -> tm          (* (t1, t2) *)
  | tfst : tm -> tm                 (* fst t1 *)
  | tsnd : tm -> tm                 (* snd t1 *)
  | tfix : tm -> tm                 (* fix t *)
  | tformula : formula -> tm        (* f *)
  | tif : formula -> tm -> tm -> tm (* if f then t1 else t2 *)
  .

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tunit" 
  | Case_aux c "tpair" | Case_aux c "tfst" | Case_aux c "tsnd" 
  | Case_aux c "tfix"  | Case_aux c "tformula" | Case_aux c "tif"
  ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (tabs x T t)
  | v_unit : value tunit 
  | v_pair : forall t1 t2, value (tpair t1 t2)
  | v_formula : forall f, value (tformula f)
  .

Tactic Notation "v_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "v_abs" | Case_aux c "v_unit"
  | Case_aux c "v_pair" | Case_aux c "v_formula"
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
  | tfix t1 => tfix ([x:=s] t1)
  | tformula f => tformula f
  | tif f t1 t2 => tif f ([x:=s] t1) ([x:=s] t2)
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
  | ST_Fix : forall t,
      tfix t ==> tapp t (tfix t)
  | ST_IfAbs : forall f T x1 x2 t1 t2,
      tif f (tabs x1 T t1) (tabs x2 T t2) ==>
        tabs x T (tif f (tapp (tabs x1 T t1) (tvar x)) (tapp (tabs x2 T t2) (tvar x)))
  | ST_IfUnit : forall f,
      tif f tunit tunit ==> tunit
  | ST_IfPair : forall f t11 t12 t21 t22,
      tif f (tpair t11 t12) (tpair t21 t22) ==> tpair (tif f t11 t21) (tif f t12 t22)
  | ST_IfFormula : forall f f1 f2,
      tif f (tformula f1) (tformula f2) ==> tformula (fite f f1 f2)
  | ST_IfLeft : forall f t1 t1' t2,
      t1 ==> t1' ->
      tif f t1 t2 ==> tif f t1' t2
  | ST_IfRight : forall f t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tif f t1 t2 ==> tif f t1 t2'

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App" 
  | Case_aux c "ST_FstPair" | Case_aux c "ST_Fst"
  | Case_aux c "ST_SndPair" | Case_aux c "ST_Snd"
  | Case_aux c "ST_Fix" | Case_aux c "ST_IfAbs"
  | Case_aux c "ST_IfUnit" | Case_aux c "ST_IfPair"
  | Case_aux c "ST_IfFormula"
  | Case_aux c "ST_IfLeft" | Case_aux c "ST_IfRight"
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
  | T_Fix : forall Gamma t T,
       Gamma |- t \in (TArrow T T) ->
       Gamma |- tfix t \in T
  | T_Formula : forall Gamma f,
       Gamma |- tformula f \in TFormula
  | T_If : forall Gamma f t1 t2 T,
       Gamma |- t1 \in T ->
       Gamma |- t2 \in T ->
       Gamma |- tif f t1 t2 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_Unit" 
  | Case_aux c "T_Pair" | Case_aux c "T_Fst" | Case_aux c "T_Snd" 
  | Case_aux c "T_Fix"
  | Case_aux c "T_Formula" | Case_aux c "T_If"
  ].

Hint Constructors has_type.

End Smtrg.

