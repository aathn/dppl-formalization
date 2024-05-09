From TLC Require Import LibLN.
From DPPL Require Import Syntax.

(*********************************)
(** TYPING RELATION DEFINITIONS **)
(*********************************)

Definition const_type (c : const) (m : modifier) :=
  match c with
  | CReal _ => TyReal
  | CAdd => TyArr m (TyProd TyReal TyReal) TyReal
  end.

Definition dist_type (d : dist) (m : modifier) :=
  match d with
  | DNormal => (TyProd TyReal TyReal, TyReal)
  end.

Reserved Notation "Gamma |= t ~: m , T " (at level 50).
Inductive has_type : env -> term -> modifier -> type -> Prop :=
| TVar Gamma x m T :
    (* ok Gamma -> *)
    binds x T Gamma ->
    Gamma |= TmFVar x ~: m, T
| TLam L Gamma T1 T2 t m m':
    (forall x, x \notin L ->
          (Gamma & x ~ T1) |= [0 ~> TmFVar x]t ~: m, T2) ->
    Gamma |= TmLam T1 t ~: m', TyArr m T1 T2
| TApp Gamma T1 T2 t1 t2 m :
    Gamma |= t1 ~: m, TyArr m T1 T2 ->
    Gamma |= t2 ~: m, T1 ->
    Gamma |= TmApp t1 t2 ~: m, T2
| TConst Gamma c m m' :
    Gamma |= TmConst c ~: m, const_type c m'
| TUnit Gamma m :
    Gamma |= TmUnit ~: m, TyUnit
| TProd Gamma T1 T2 t1 t2 m :
    Gamma |= t1 ~: m, T1 ->
    Gamma |= t2 ~: m, T2 ->
    Gamma |= TmPair t1 t2 ~: m, TyProd T1 T2
| TFst Gamma T1 T2 t m :
    Gamma |= t ~: m, TyProd T1 T2 ->
    Gamma |= TmFst t ~: m, T1
| TSnd Gamma T1 T2 t m :
    Gamma |= t ~: m, TyProd T1 T2 ->
    Gamma |= TmSnd t ~: m, T2
| TIf Gamma T t1 t2 t3 m :
    Gamma |= t1 ~: m, TyReal ->
    Gamma |= t2 ~: m, T ->
    Gamma |= t3 ~: m, T ->
    Gamma |= TmIf t1 t2 t3 ~: m, T
| TDist Gamma T1 T2 d t m m' :
    dist_type d m' = (T1, T2) ->
    Gamma |= t ~: m, T1 ->
    Gamma |= TmDist d t ~: m, TyDist T2
| TAssume Gamma T t :
    Gamma |= t ~: Rnd, TyDist T ->
    Gamma |= TmAssume t ~: Rnd, T
| TWeight Gamma t :
    Gamma |= t ~: Rnd, TyReal ->
    Gamma |= TmWeight t ~: Rnd, TyUnit
where " Gamma |= t ~: m , T " := (has_type Gamma t m T).

#[export]
 Hint Constructors has_type : core.
