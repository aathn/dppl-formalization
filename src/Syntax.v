From TLC Require Import LibLN.
From Coq Require Import Reals.

(************************)
(** SYNTAX DEFINITIONS **)
(************************)

Inductive modifier : Type :=
| Det
| Rnd.

Inductive type : Type :=
| TyReal
| TyUnit
| TyArr (m : modifier) (T1 : type) (T2 : type)
| TyProd (T1 : type) (T2 : type)
| TyDist (T : type).

Inductive const : Type :=
| CAdd.

Inductive dist : Type :=
| DNormal.

Inductive term : Type :=
| TmBVar (x : nat)
| TmFVar (x : var)
| TmLam  (T : type) (t : term)
| TmApp  (t1 : term) (t2 : term)
| TmReal (r : R)
| TmConst (c : const)
| TmUnit
| TmPair (t1 : term) (t2 : term)
| TmFst (t : term)
| TmSnd (t : term)
| TmIf (t1 : term) (t2 : term) (t3 : term)
| TmDist (D : dist) (t : term)
| TmAssume (t : term)
| TmWeight (t : term).

Inductive value : term -> Prop :=
| VLam T t : value (TmLam T t)
| VConst c : value (TmConst c)
| VReal r : value (TmReal r)
| VUnit : value TmUnit
| VPair v1 v2 :
    value v1 ->
    value v2 ->
    value (TmPair v1 v2)
| VDist d v :
    value v ->
    value (TmDist d v).
#[export]
 Hint Constructors value : core.

Fixpoint fv (t : term) :=
  match t with
  | TmBVar _ => \{}
  | TmFVar x => \{x}
  | TmLam T t' => fv t'
  | TmApp t1 t2 => fv t1 \u fv t2
  | TmReal _ => \{}
  | TmConst _ => \{}
  | TmUnit => \{}
  | TmPair t1 t2 => fv t1 \u fv t2
  | TmFst t' => fv t'
  | TmSnd t' => fv t'
  | TmIf t1 t2 t3 => fv t1 \u fv t2 \u fv t3
  | TmDist _ t => fv t
  | TmAssume t => fv t
  | TmWeight t => fv t
  end.

Reserved Notation "[ k ~> u ] t" (at level 67).
Fixpoint open (k : nat) (u : term) (t : term) :=
  match t with
  | TmBVar i => (If i = k then u else t)
  | TmFVar _ => t
  | TmLam T t' => TmLam T ([S k ~> u]t')
  | TmApp t1 t2 => TmApp ([k ~> u]t1) ([k ~> u]t2)
  | TmReal _ => t
  | TmConst c => TmConst c
  | TmUnit => TmUnit
  | TmPair t1 t2 => TmPair ([k ~> u]t1) ([k ~> u]t2)
  | TmFst t' => TmFst ([k ~> u]t')
  | TmSnd t' => TmSnd ([k ~> u]t')
  | TmIf t1 t2 t3 => TmIf ([k ~> u]t1) ([S k ~> u]t2) ([k ~> u]t3)
  | TmDist d t => TmDist d ([k ~> u]t)
  | TmAssume t => TmAssume ([k ~> u]t)
  | TmWeight t => TmWeight ([k ~> u]t)
  end
where "[ k ~> u ] t " := (open k u t).
#[export]
 Hint Unfold open : core.

Reserved Notation "[ x => u ] t" (at level 67).
Fixpoint subst (x : var) (u : term) (t : term) :=
  match t with
  | TmBVar _ => t
  | TmFVar y => (If x = y then u else t)
  | TmLam T t' => TmLam T ([x => u]t')
  | TmApp t1 t2 => TmApp ([x => u]t1) ([x => u]t2)
  | TmReal r => TmReal r
  | TmConst c => TmConst c
  | TmUnit => TmUnit
  | TmPair t1 t2 => TmPair ([x => u]t1) ([x => u]t2)
  | TmFst t' => TmFst ([x => u]t')
  | TmSnd t' => TmSnd ([x => u]t')
  | TmIf t1 t2 t3 => TmIf ([x => u]t1) ([x => u]t2) ([x => u]t3)
  | TmDist d t => TmDist d ([x => u]t)
  | TmAssume t => TmAssume ([x => u]t)
  | TmWeight t => TmWeight ([x => u]t)
  end
where "[ x => u ] t" := (subst x u t).
#[export]
 Hint Unfold subst : core.

Definition env := env type.

(**********************************)
(** TACTICS FOR LOCALLY NAMELESS **)
(**********************************)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : term => fv x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; intuition eauto.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.
