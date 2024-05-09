From Coq Require Import Reals.
From DPPL Require Import Syntax.
From TLC Require Import LibList.

Inductive eval_context : (term -> term) -> Prop :=
| ECAppL t' : eval_context (fun t => TmApp t t')
| ECAppR v :
    value v ->
    eval_context (fun t => TmApp v t)
| ECPairL t2 : eval_context (fun t1 => TmPair t1 t2)
| ECPairR v :
    value v ->
    eval_context (fun t => TmPair v t)
| ECFst : eval_context (fun t => TmFst t)
| ECSnd : eval_context (fun t => TmSnd t)
| ECIfCond t1 t2 : eval_context (fun t => TmIf t t1 t2)
| ECDist d : eval_context (fun t => TmDist d t)
| ECAssume : eval_context (fun t => TmAssume t)
| ECWeight : eval_context (fun t => TmWeight t).
#[export]
 Hint Constructors eval_context : core.

Definition const_eval (c : const) (t : term) :=
  match c, t with
  | CAdd, TmPair (TmConst (CReal c1)) (TmConst (CReal c2)) =>
      Some (TmConst (CReal (c1 + c2)))
  | _, _ => None
  end.

Reserved Notation "t1 -->d t2" (at level 50).
Inductive eval_step_det : term -> term -> Prop :=
| EApp T t v :
    value v ->
    TmApp (TmLam T t) v -->d [0 ~> v]t
| EConstApp c v1 v2 :
    value v2 ->
    const_eval c v2 = Some v1 ->
    TmApp (TmConst c) v2 -->d v1
| EIfTrue c t1 t2 :
    (c > 0)%R ->
    TmIf (TmConst (CReal c)) t1 t2 -->d t1
| EIfFalse c t1 t2 :
    (c <= 0)%R ->
    TmIf (TmConst (CReal c)) t1 t2 -->d t2
| EFst v1 v2 :
    value v1 ->
    value v2 ->
    TmFst (TmPair v1 v2) -->d v1
| ESnd v1 v2 :
    value v1 ->
    value v2 ->
    TmFst (TmPair v1 v2) -->d v2
| ECongD E t1 t2 :
    eval_context E ->
    t1 -->d t2 ->
    E t1 -->d E t2
where "t1 -->d t2" := (eval_step_det t1 t2).
#[export]
 Hint Constructors eval_step_det : core.

Parameter inverse_cdf : dist -> term -> R -> term.

Reserved Notation "t -->r t'" (at level 50).
Inductive eval_step_rnd : term * R * list R -> term * R * list R -> Prop :=
| EDet t t' w s :
  t -->d t' ->
  (t, w, s) -->r (t', w, s)
| EWeight w s c :
  (c >= 0)%R ->
  (TmWeight (TmConst (CReal c)), w, s) -->r (TmUnit, (c * w)%R, s)
| EAssume w p s d v :
  value v ->
  (TmAssume (TmDist d v), w, (p :: s)) -->r (inverse_cdf d v p, w, s)
| ECongR E t w s t' w' s' :
    eval_context E ->
    (t, w, s) -->r (t', w', s') ->
    (E t, w, s) -->r (E t', w', s')
where "t -->r t'" := (eval_step_rnd t t').
#[export]
 Hint Constructors eval_step_det : core.
