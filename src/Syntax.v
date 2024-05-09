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
| CReal (r : R)
| CAdd.

Inductive dist : Type :=
| DNormal.

Inductive term : Type :=
| TmBVar (x : nat)
| TmFVar (x : var)
| TmLam  (T : type) (t : term)
| TmApp  (t1 : term) (t2 : term)
| TmConst (c : const)
| TmUnit
| TmPair (t1 : term) (t2 : term)
| TmFst (t : term)
| TmSnd (t : term)
| TmIf (t1 : term) (t2 : term) (t3 : term)
| TmDist (D : dist) (t : term)
| TmAssume (t : term)
| TmWeight (t : term).
