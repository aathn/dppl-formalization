From TLC Require Import LibLN LibList LibEnv.
From DPPL Require Import Syntax.
Import LibListNotation.

(*********************************)
(** TYPING RELATION DEFINITIONS **)
(*********************************)

Definition prim_type (phi : prim) :=
  match phi with
  | PAdd | PMul => (TyReal A :: [TyReal A], TyReal A)
  | PWiener p => (TyReal C :: [], TyReal C)
  end.

Definition dist_type (d : dist) :=
  match d with
  | DNormal | DBeta => (TyReal C :: [TyReal C], TyReal C)
  end.

Declare Scope coeffect_scope.
Definition coeffect_mul (c1 : coeffect) (c2 : coeffect) :=
  match c1, c2 with
  | A, c | c, A => c
  | B, B => B
  | C, _ | _, C => C
  end.
Notation " c1 * c2 " := (coeffect_mul c1 c2) : coeffect_scope.

Declare Scope effect_scope.
Definition effect_mul (e1 : effect) (e2 : effect) :=
  match e1, e2 with
  | Det, e | e, Det => e
  | Rnd, _ => Rnd
  end.
Notation " e1 * e2 " := (effect_mul e1 e2) : effect_scope.

Declare Scope coeffect_type_scope.
Fixpoint coeffect_type_mul (c : coeffect) (T : type) :=
  let coeffect_type_mul_list := fix f (Ts : list type) :=
      match Ts with
      | nil => nil
      | T :: Ts => (coeffect_type_mul c T) :: (f Ts)
      end
  in
  match T with
  | TyReal c' => TyReal (coeffect_mul c c')
  | TyTuple Ts => TyTuple (coeffect_type_mul_list Ts)
  | T => T
  end.
Notation " c .* T " := (coeffect_type_mul c T) (at level 50) : coeffect_type_scope.

Declare Scope coeffect_env_scope.
Fixpoint coeffect_env_mul (c : coeffect) (Gamma : env) :=
  match Gamma with
  | nil => nil
  | ((x, T) :: Gamma) => coeffect_env_mul c Gamma & x ~ coeffect_type_mul c T
  end.
Notation " c .* Gamma " := (coeffect_env_mul c Gamma) : coeffect_env_scope.

Declare Scope env_scope.
Fixpoint env_add (G1 : env) (G2 : env) :=
  match G1 with
  | nil => Some G2
  | (x, T) :: G1 =>
    match get x G2 with
    | Some T' => If T = T' then env_add G1 G2 else None
    | None => LibOption.map (fun G => (x, T) :: G) (env_add G1 G2)
    end
  end.
Notation " Gamma1 + Gamma2 " := (env_add Gamma1 Gamma2) : env_scope.

Open Scope coeffect_scope.
Open Scope coeffect_scope.
Bind Scope effect_scope with effect.
Open Scope effect_scope.
Open Scope coeffect_type_scope.
Open Scope coeffect_env_scope.

Definition prod_effect (es : list effect) := fold_left effect_mul Det es.

Definition prod_coeffect (cs : list coeffect) := fold_left coeffect_mul A cs.

Definition sum_env (Gammas : list env) :=
  fold_left
    (fun Gamma1 Gamma2 => LibOption.apply (env_add Gamma1) Gamma2)
    (Some nil) Gammas.

Definition Forall4 {A B C D} (P : A->B->C->D->Prop)
  (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D) :=
  Forall2 (fun '(a, b) '(c, d) => P a b c d) (combine l1 l2) (combine l3 l4).

#[export]
Instance Inhab_type : Inhab type.
Proof. apply (Inhab_of_val (TyUnit)). Qed.

#[export]
Instance Inhab_term : Inhab term.
Proof. apply (Inhab_of_val (TmUnit)). Qed.

#[export]
Instance Inhab_effect : Inhab effect.
Proof. apply (Inhab_of_val Det). Qed.

Reserved Notation "Gamma |= t ~: m , T " (at level 50).
Inductive has_type : env -> term -> effect -> type -> Prop :=
| TVar Gamma x T :
    (* ok Gamma -> *)
    binds x T Gamma ->
    Gamma |= TmFVar x ~: Det, T
| TAbs L Gamma T1 T2 t e:
    (forall x, x \notin L ->
          (Gamma & x ~ T1) |= [0 ~> TmFVar x]t ~: e, T2) ->
    Gamma |= TmAbs T1 t ~: Det, TyArr e T1 T2
| TApp Gamma1 Gamma2 Gamma T1 T2 t1 t2 e1 e2 e3 :
    Gamma1 |= t1 ~: e1, TyArr e3 T1 T2 ->
    Gamma2 |= t2 ~: e2, T1 ->
    Gamma1 + Gamma2 = Some Gamma ->
    Gamma |= TmApp t1 t2 ~: e1 * e2 * e3, T2
| TPrimApp Gamma phi T Gammas ts es Ts :
    prim_type phi = (Ts, T) ->
    all_has_type Gammas ts es Ts ->
    sum_env Gammas = Some Gamma ->
    Gamma |= TmPrimApp phi ts ~: prod_effect es, T
| TReal Gamma r :
    Gamma |= TmReal r ~: Det, TyReal C
| TTuple Gamma Gammas Ts ts es :
    all_has_type Gammas ts es Ts ->
    sum_env Gammas = Some Gamma ->
    Gamma |= TmTuple ts ~: prod_effect es, TyTuple Ts
| TProj Gamma n i t e T Ts :
    Gamma |= t ~: e, TyTuple Ts ->
    length Ts = n -> i < n ->
    Nth i Ts T ->
    Gamma |= TmProj n i t ~: e, T
| TIf Gamma T t1 t2 t3 e1 e2 e3:
    Gamma |= t1 ~: e1, TyReal B ->
    Gamma |= t2 ~: e2, T ->
    Gamma |= t3 ~: e3, T ->
    Gamma |= TmIf t1 t2 t3 ~: e1 * e2 * e3, T
| TDiff Gamma1 Gamma2 Gamma T1 T2 t1 t2 e1 e2 c d:
  (d = FA -> c = A) ->
  (d = FB -> c = B) ->
  real_structure T1 ->
  real_structure T2 ->
  Gamma1 |= t1 ~: e1, TyArr Det (subs_coeffects c T1) T2 ->
  Gamma2 |= t2 ~: e2, subs_coeffects c T1 ->
  Gamma1 + Gamma2 = Some Gamma ->
  Gamma |= TmDiff d t1 t2 ~: e1 * e2, TyArr Det (subs_coeffects A T1) T2
| TDist Gamma T Gammas d Ts ts es :
    dist_type d = (Ts, T) ->
    all_has_type Gammas ts es Ts ->
    Gamma |= TmDist d ts ~: prod_effect es, TyDist T
| TAssume Gamma T t e :
    Gamma |= t ~: e, TyDist T ->
    Gamma |= TmAssume t ~: (Rnd * e), T
| TWeight Gamma t e :
    Gamma |= t ~: e, TyReal C->
    Gamma |= TmWeight t ~: (Rnd * e), TyUnit
| TInfer Gamma t T e :
    Gamma |= t ~: e, TyArr Rnd (TyTuple nil) T ->
    Gamma |= TmInfer t ~: e, TyDist T
where " Gamma |= t ~: m , T " := (has_type Gamma t m T)

with all_has_type : list env -> list term -> list effect -> list type -> Prop :=
| TNil : all_has_type nil nil nil nil
| TCons Gamma t e T Gammas ts es Ts :
  Gamma |= t ~: e , T ->
  all_has_type Gammas ts es Ts ->
  all_has_type (Gamma :: Gammas) (t :: ts) (e :: es) (T :: Ts)
.

#[export]
 Hint Constructors has_type : core.
