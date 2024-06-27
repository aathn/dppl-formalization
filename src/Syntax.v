From TLC Require Import LibLN LibList.
From Coq Require Import Reals.

(************************)
(** SYNTAX DEFINITIONS **)
(************************)

Inductive coeffect : Set :=
| A
| B
| C.

Inductive effect : Set :=
| Det
| Rnd.

Inductive type : Set :=
| TyReal (c : coeffect)
| TyArr (e : effect) (T1 : type) (T2 : type)
| TyTuple (Ts : list type)
| TyDist (T : type).

Inductive real_structure : type -> Prop :=
| RSReal (c : coeffect) : real_structure (TyReal c)
| RSTuple (Ts : list type) :
  Forall real_structure Ts -> real_structure (TyTuple Ts).

Fixpoint subs_coeffects (c : coeffect) (T : type) :=
  let subs_coeffects_list := fix f (Ts : list type) :=
      match Ts with
      | nil => nil
      | T :: Ts => subs_coeffects c T :: f Ts
      end
  in
  match T with
  | TyReal _ => TyReal c
  | TyTuple Ts => TyTuple (subs_coeffects_list Ts)
  | T => T
  end.

Inductive prim : Set :=
| PAdd
| PMul
| PWiener (p : R).

Inductive dist : Set :=
| DNormal
| DBeta.

Inductive diff_flag : Set :=
| FA
| FB.

Inductive term : Set :=
| TmBVar (x : nat)
| TmFVar (x : var)
| TmAbs  (T : type) (t : term)
| TmApp  (t1 : term) (t2 : term)
| TmPrimApp (phi : prim) (ts : list term)
| TmReal (r : R)
| TmTuple (ts : list term)
| TmProj (n : nat) (i : nat) (t : term)
| TmIf (t1 : term) (t2 : term) (t3 : term)
| TmDist (D : dist) (ts : list term)
| TmAssume (t : term)
| TmWeight (t : term)
| TmInfer (t : term)
| TmDiff (d : diff_flag) (t1 : term) (t2 : term)
| TmSolve (t1 : term) (t2 : term) (t3 : term).

Inductive value : term -> Prop :=
| VAbs T t : value (TmAbs T t)
| VPrimApp (phi : prim) (vs : list term) :
  Forall value vs -> value (TmPrimApp phi vs)
| VReal r : value (TmReal r)
| VPair (vs : list term) :
  Forall value vs -> value (TmTuple vs)
| VDist d vs :
  Forall value vs -> value (TmDist d vs)
| VInfer v :
    value v ->
    value (TmInfer v).
#[export]
 Hint Constructors value : core.

(* Syntatic sugar *)
Definition TyUnit := TyTuple nil.
Definition TmUnit := TmTuple nil.

Fixpoint fv (t : term) :=
  let fv_list := fix f (ts : list term) :=
    match ts with
    | nil => \{}
    | t :: ts => fv t \u f ts
    end
  in
  match t with
  | TmBVar _ => \{}
  | TmFVar x => \{x}
  | TmAbs T t => fv t
  | TmApp t1 t2 => fv t1 \u fv t2
  | TmPrimApp phi ts => fv_list ts
  | TmReal _ => \{}
  | TmTuple ts => fv_list ts
  | TmProj n i t => fv t
  | TmIf t1 t2 t3 => fv t1 \u fv t2 \u fv t3
  | TmDist _ ts => fv_list ts
  | TmAssume t => fv t
  | TmWeight t => fv t
  | TmInfer t => fv t
  | TmDiff _ t1 t2 => fv t1 \u fv t2
  | TmSolve t1 t2 t3 => fv t1 \u fv t2 \u fv t3
  end.

Reserved Notation "[ k ~> u ] t" (at level 67).
Fixpoint open (k : nat) (u : term) (t : term) :=
  let open_list := fix f (ts : list term) :=
    match ts with
    | nil => nil
    | t :: ts => ([k ~> u] t) :: f ts
    end
  in
  match t with
  | TmBVar i => (If i = k then u else t)
  | TmFVar _ => t
  | TmAbs T t' => TmAbs T ([S k ~> u]t')
  | TmApp t1 t2 => TmApp ([k ~> u]t1) ([k ~> u]t2)
  | TmReal _ => t
  | TmPrimApp phi ts => TmPrimApp phi (open_list ts)
  | TmTuple ts => TmTuple (open_list ts)
  | TmProj n i t' => TmProj n i ([k ~> u]t')
  | TmIf t1 t2 t3 => TmIf ([k ~> u]t1) ([S k ~> u]t2) ([k ~> u]t3)
  | TmDist d ts => TmDist d (open_list ts)
  | TmAssume t => TmAssume ([k ~> u]t)
  | TmWeight t => TmWeight ([k ~> u]t)
  | TmInfer t => TmInfer ([k ~> u]t)
  | TmDiff d t1 t2 => TmDiff d ([k ~> u]t1) ([k ~> u]t2)
  | TmSolve t1 t2 t3 => TmSolve ([k ~> u]t1) ([k ~> u]t2) ([k ~> u]t3)
  end
where "[ k ~> u ] t " := (open k u t).
#[export]
 Hint Unfold open : core.

Reserved Notation "[ x => u ] t" (at level 67).
Fixpoint subst (x : var) (u : term) (t : term) :=
  let subst_list := fix f (ts : list term) :=
    match ts with
    | nil => nil
    | t :: ts => ([x => u] t) :: f ts
    end
  in
  match t with
  | TmBVar _ => t
  | TmFVar y => (If x = y then u else t)
  | TmAbs T t' => TmAbs T ([x => u]t')
  | TmApp t1 t2 => TmApp ([x => u]t1) ([x => u]t2)
  | TmReal r => TmReal r
  | TmPrimApp phi ts => TmPrimApp phi (subst_list ts)
  | TmTuple ts => TmTuple (subst_list ts)
  | TmProj n i t => TmProj n i ([x => u]t)
  | TmIf t1 t2 t3 => TmIf ([x => u]t1) ([x => u]t2) ([x => u]t3)
  | TmDist d ts => TmDist d (subst_list ts)
  | TmAssume t => TmAssume ([x => u]t)
  | TmWeight t => TmWeight ([x => u]t)
  | TmInfer t => TmInfer ([x => u]t)
  | TmDiff d t1 t2 => TmDiff d ([x => u]t1) ([x => u]t2)
  | TmSolve t1 t2 t3 => TmSolve ([x => u]t1) ([x => u]t2) ([x => u]t3)
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
