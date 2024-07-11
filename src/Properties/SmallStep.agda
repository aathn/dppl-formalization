module Properties.SmallStep (ℝ : Set) where

-- Minor lemmas about the step relations (and typing)

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature

open import Function using (_$_ ; const)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Product using (∃-syntax)
open import Data.Vec.Functional using (map ; updateAt)
open import Data.Vec.Functional.Properties using (updateAt-id-local)

open import Syntax ℝ
open import Typing ℝ
open import SmallStep ℝ

-- Congruence

cong-step
  : ∀ {A B _↝_ F o ts a t′ b} n
  → evaluable o n ≡ true
  → (∀ i → i <ꟳ n → Value (ts i))
  → CongCls {A} {B} _↝_ F (F (ts n) a) (F t′ b)
  → -------------------------------------------
    CongCls _↝_ F
      (F (op (o , ts)) a)
      (F (op (o , updateAt ts n (const t′))) b)

cong-step {F = F} {o} {ts} {a} {t′} {b} n Hev Hvs Hstep =
  subst
    (λ ts′ → CongCls _ F (F (op (o , ts′)) a)
                         (F (op (o , updateAt ts n (const t′))) b))
    (funext $ updateAt-id-local n ts refl)
    (econg (ectx Hev Hvs) Hstep)

cong-step′
  : ∀ {_↝_ o ts t′} n
  → evaluable o n ≡ true
  → (∀ i → i <ꟳ n → Value (ts i))
  → CongCls _↝_ const (ts n) t′
  → -------------------------------------
    CongCls _↝_ const
      (op (o , ts))
      (op (o , updateAt ts n (const t′)))

cong-step′ = cong-step {a = tt} {b = tt}


-- Canonical forms

canonical-⇒
  : ∀ {Γ t e e′ T T₁ T₂}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ T₁ ⇒[ e′ ] T₂
  → -----------------------------
    ∃[ T′ ] ∃[ t′ ] t ≡ abs T′ t′

canonical-⇒ (tabs _) _ refl = _ , _ , refl
canonical-⇒ (tweaken Htype _ _) Hval Heq =
  canonical-⇒ Htype Hval Heq
canonical-⇒ (tsub Htype _ (sarr _ _ _)) Hval refl =
  canonical-⇒ Htype Hval refl
canonical-⇒ (tpromote {T = _ ⇒[ _ ] _} Htype H≤) Hval Heq =
  canonical-⇒ Htype Hval Heq

canonical-real
  : ∀ {Γ t e T c}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ treal c
  → -----------------
    ∃[ r ] t ≡ real r

canonical-real treal _ _ = _ , refl
canonical-real (tweaken Htype _ _) Hval Heq =
  canonical-real Htype Hval Heq
canonical-real (tsub Htype _ (sreal _)) Hval refl =
  canonical-real Htype Hval refl
canonical-real (tpromote {T = treal _} Htype H≤) Hval refl =
  canonical-real Htype Hval refl

canonical-tup
  : ∀ {Γ t e T n Ts}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ ttup {n} Ts
  → -------------------------------------------
    ∃[ ts ] t ≡ tup {n} ts × ∀ i → Value (ts i)

canonical-tup (ttup _ _) (vtup Hvs) refl = _ , refl , Hvs
canonical-tup (tweaken Htype _ _) Hval Heq =
  canonical-tup Htype Hval Heq
canonical-tup (tsub Htype _ (stup _)) Hval refl =
  canonical-tup Htype Hval refl
canonical-tup (tpromote {T = ttup _} Htype H≤) Hval refl =
  canonical-tup Htype Hval refl

canonical-dist
  : ∀ {Γ t e T T′}
  → Γ ⊢ t :[ e ] T
  → Value t
  → T ≡ tdist T′
  → -----------------------------------------
    (∃[ D ] ∃[ rs ] t ≡ dist D (map real rs))
  ⊎ (∃[ v ] t ≡ infer v × Value (v ₀))

canonical-dist (tdist {ts = ts} _ Htypes _) (vdist Hvs) _ =
  let Hreals : ∃[ rs ] ts ≡ map real rs
      Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
  in
  case Hreals λ { (_ , refl) → ι₁ $ _ , _ , refl }
canonical-dist (tinfer _) (vinfer Hv) refl = ι₂ $ _ , refl , Hv
canonical-dist (tweaken Htype _ _) Hval Heq =
  canonical-dist Htype Hval Heq
canonical-dist (tsub Htype _ (sdist _)) Hval refl =
  canonical-dist Htype Hval refl
canonical-dist (tpromote {T = tdist _} Htype H≤) Hval Heq =
  canonical-dist Htype Hval Heq

val-type-det
  : ∀ {Γ t e T}
  → Γ ⊢ t :[ e ] T
  → Value t
  → ----------------
    Γ ⊢ t :[ det ] T
val-type-det (tabs Htype) _ = tabs Htype
val-type-det treal _ = treal
val-type-det (ttup Htypes Hd) (vtup Hvs) =
  ttup (λ i → val-type-det (Htypes i) (Hvs i)) Hd
val-type-det (tdist HD Htypes Hd) (vdist Hvs) =
  tdist HD (λ i → val-type-det (Htypes i) (Hvs i)) Hd
val-type-det (tinfer Htype) (vinfer Hval) = tinfer (val-type-det Htype Hval)
val-type-det (tweaken Htype H⊆ Hd) Hval = tweaken (val-type-det Htype Hval) H⊆ Hd
val-type-det (tsub Htype He Hsub) Hval = tsub (val-type-det Htype Hval) 0≤ Hsub
val-type-det (tpromote Htype H≤) Hval = tpromote (val-type-det Htype Hval) H≤


module Step (Ass : EvalAssumptions) where
  open Eval Ass

  →det⊆→rnd
    : ∀ {t t′ w s}
    → t →det t′
    → -----------------------------
      (t , w , s) →rnd (t′ , w , s)

  →det⊆→rnd (estep Hstep) = estep (edet Hstep)
  →det⊆→rnd (econg ctx Hstep) = econg ctx (→det⊆→rnd Hstep)
