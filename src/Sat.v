
Require Export SfLib.

Module Sat.

Inductive boolean : Type :=
  | btrue : boolean 
  | bfalse : boolean
  .

Tactic Notation "boolean_cases" tactic(first) ident(c) :=
  first; [ Case_aux c "btrue" | Case_aux c "bfalse" ].

Inductive formula : Type :=
  | fval : boolean -> formula
  | fvar : id -> formula
  | fite : formula -> formula -> formula -> formula
  .

Tactic Notation "formula_cases" tactic(first) ident(c) :=
  first; [ Case_aux c "fval" | Case_aux c "fvar" | Case_aux c "fite" ].  

Notation ftrue := (fval btrue).
Notation ffalse := (fval bfalse).

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Definition model : Type := (id -> boolean).

Fixpoint evaluate (f : formula) (m : model) : boolean :=
  match f with
  | fval b => b
  | fvar x => m x
  | fite p a b => match evaluate p m with
                  | btrue => evaluate a m
                  | bfalse => evaluate b m
                  end
  end.

Definition satisfies (f : formula) (m : model) : Prop :=
  evaluate f m = btrue 
  .

Definition satisfiable (f : formula) : Prop :=
  exists (m : model), satisfies f m
  .

Definition unsatisfiable (f : formula) : Prop := not (satisfiable f)
  .
  
Inductive appears_free_in : id -> formula -> Prop :=
  | afi_var : forall x, appears_free_in x (fvar x)
  | afi_ite1 : forall x t1 t2 t3,
      appears_free_in x t1 -> appears_free_in x (fite t1 t2 t3)
  | afi_ite2 : forall x t1 t2 t3,
      appears_free_in x t2 -> appears_free_in x (fite t1 t2 t3)
  | afi_ite3 : forall x t1 t2 t3,
      appears_free_in x t3 -> appears_free_in x (fite t1 t2 t3)
  .

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_ite1" | Case_aux c "afi_ite2" | Case_aux c "afi_ite3"
  ].

Hint Constructors appears_free_in.

End Sat.

