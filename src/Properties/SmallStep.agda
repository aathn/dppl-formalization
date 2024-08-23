open import Lib.Reals

module Properties.SmallStep (R : Reals₀) where

open Reals R hiding (refl)
open Interval R

-- Minor lemmas about the step relations (and typing)

open import Lib.Prelude
open import Lib.FunExt
open import Lib.BindingSignature
open import Lib.EvalCtx

import Data.List as L
open import Data.Product using (map₁)
open import Data.Vec.Functional using (map ; updateAt)
open import Data.Vec.Functional.Properties using (updateAt-updates)
open import Relation.Nullary using (Irrelevant)

open import Syntax R
open import Typing R
open import SmallStep R

-- Value t is irrelevant

value-irrelevant :
  {t : Term}
  → --------------------
  Irrelevant (IsValue t)

value-irrelevant vlam vlam = refl
value-irrelevant vreal vreal = refl
value-irrelevant (vtup vs) (vtup vs′) =
  ap vtup (funext λ i → value-irrelevant (vs i) (vs′ i))
value-irrelevant (vdist vs) (vdist vs′) =
  ap vdist (funext λ i → value-irrelevant (vs i) (vs′ i))
value-irrelevant (vinfer v) (vinfer v′) =
  ap vinfer (value-irrelevant v v′)

-- Canonical forms

canonical-⇒ :
  {Γ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e e′ : Eff}
  {T T₁ T₂ : Type}
  (_ : Γ ⊢[ c ] t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ T₁ ⇒[ e′ ] T₂)
  → -----------------------------
  ∃ λ T′ → ∃ λ t′ → t ≡ lam T′ t′

canonical-⇒ (tlam _) _ refl = _ , _ , refl
canonical-⇒ (tsub Htype _ (sarr _ _ _)) Hval refl =
  canonical-⇒ Htype Hval refl
canonical-⇒ (tpromote {T = _ ⇒[ _ ] _} Htype H≤) Hval Heq =
  canonical-⇒ Htype Hval Heq
canonical-⇒ (tdemote  {T = _ ⇒[ _ ] _} Htype H≤) Hval Heq =
  canonical-⇒ Htype Hval Heq

canonical-real :
  {Γ : TyEnv}
  {c d : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ ⊢[ d ] t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ treal c)
  → -----------------------
  ∃ λ r → t ≡ real r

canonical-real (treal _) _ _ = _ , refl
canonical-real (tsub Htype _ (sreal _)) Hval refl =
  canonical-real Htype Hval refl
canonical-real (tpromote {T = treal _} Htype H≤) Hval refl =
  canonical-real Htype Hval refl
canonical-real (tdemote {T = treal _} Htype H≤) Hval refl =
  canonical-real Htype Hval refl

canonical-tup :
  {Γ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  {n : ℕ}
  {Ts : Vector Type n}
  (_ : Γ ⊢[ c ] t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ ttup {n} Ts)
  → --------------------------------------------
  ∃ λ ts → t ≡ tup {n} ts × ∀ i → IsValue (ts i)

canonical-tup (ttup _ _) (vtup Hvs) refl = _ , refl , Hvs
canonical-tup (tsub Htype _ (stup _)) Hval refl =
  canonical-tup Htype Hval refl
canonical-tup (tpromote {T = ttup _} Htype H≤) Hval refl =
  canonical-tup Htype Hval refl
canonical-tup (tdemote {T = ttup _} Htype H≤) Hval refl =
  canonical-tup Htype Hval refl

canonical-dist :
  {Γ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e : Eff}
  {T T′ : Type}
  (_ : Γ ⊢[ c ] t :[ e ] T)
  (_ : IsValue t)
  (_ : T ≡ tdist T′)
  → -------------------------------------------
    (∃ λ D → ∃ λ rs → t ≡ dist D (map real rs))
  ⊎ (∃ λ v → t ≡ infer v × IsValue (v ₀))

canonical-dist (tdist {ts = ts} _ _ Htypes) (vdist Hvs) _ =
  let Hreals : ∃ λ rs → ts ≡ map real rs
      Hreals = _ , funext λ i → π₂ $ canonical-real (Htypes i) (Hvs i) refl
  in
  case Hreals λ { (_ , refl) → ι₁ $ _ , _ , refl }
canonical-dist (tinfer _) (vinfer Hv) refl = ι₂ $ _ , refl , Hv
canonical-dist (tsub Htype _ (sdist _)) Hval refl =
  canonical-dist Htype Hval refl
canonical-dist (tpromote {T = tdist _} Htype H≤) Hval Heq =
  canonical-dist Htype Hval Heq
canonical-dist (tdemote {T = tdist _} Htype H≤) Hval Heq =
  canonical-dist Htype Hval Heq

val-type-det :
  {Γ : TyEnv}
  {c : Coeff}
  {t : Term}
  {e : Eff}
  {T : Type}
  (_ : Γ ⊢[ c ] t :[ e ] T)
  (_ : IsValue t)
  → -----------------------
  Γ ⊢[ c ] t :[ det ] T
val-type-det (tlam Htype) _ = tlam Htype
val-type-det (treal Hd) _ = treal Hd
val-type-det (ttup Hd Htypes) (vtup Hvs) =
  ttup Hd (λ i → val-type-det (Htypes i) (Hvs i))
val-type-det (tdist HD Hd Htypes) (vdist Hvs) =
  tdist HD Hd (λ i → val-type-det (Htypes i) (Hvs i))
val-type-det (tinfer Htype) (vinfer Hval) = tinfer (val-type-det Htype Hval)
val-type-det (tsub Htype He Hsub) Hval = tsub (val-type-det Htype Hval) 0≤ Hsub
val-type-det (tpromote Htype H≤) Hval = tpromote (val-type-det Htype Hval) H≤
val-type-det (tdemote Htype H≤) Hval = tdemote (val-type-det Htype Hval) H≤


module Step (Ass : EvalAssumptions) where
  open Eval Ass

  →det⊆→rnd :
    {t t′ : Term}
    {w : ℝ}
    {s : List 𝕀}
    (_ : t →det t′)
    → ---------------------------
    (t , w , s) →rnd (t′ , w , s)

  →det⊆→rnd (estep Hstep) = estep (edet Hstep)
  →det⊆→rnd (econg ctx Hstep) = econg (_ , ctx , refl) (→det⊆→rnd Hstep)

  private
    module C1 = CongStep _→ᵈ_ DetCtx id refl id
    module C2 = CongStep _→ʳ_ RndCtx map₁ refl (λ ctx → _ , ctx , refl)

  cong-stepᵈ = C1.cong-step {unit} {unit}

  cong-stepʳ = λ {ws ws′ o ts t′ n} →
    C2.cong-step {unit , ws} {unit , ws′} {o} {ts} {t′} {n}

  ctx-value-inv :
    {E : Term → Term}
    {t : Term}
    (_ : DetCtx E)
    → -----------------------
    IsValue (E t) → IsValue t

  ctx-value-inv {E} {t} (ectx {o} {j} {ts} _) Hv
    with ts' ← updateAt ts (ord {{eval-order {o}}} j) (const t) in HEt | Hv | HEt
  ... | vtup  Hvs | refl = subst IsValue (updateAt-updates j ts) (Hvs j)
  ... | vdist Hvs | refl = subst IsValue (updateAt-updates j ts) (Hvs j)
  ... | vinfer Hv₀ | refl with ₀ ← j = Hv₀

  value-cannot-step-det :
    {t t′ : Term}
    (_ : IsValue t)
    → -------------
    ¬ t →det t′

  value-cannot-step-det Hv (estep Hstep) with vlam ← Hv | () ← Hstep
  value-cannot-step-det Hv (econg Hctx Hstep) =
    value-cannot-step-det (ctx-value-inv Hctx Hv) Hstep

  value-cannot-step-rnd :
    {t t′ : Term × ℝ × List 𝕀}
    (_ : IsValue (t .π₁))
    → ------------------------
    ¬ t →rnd t′

  value-cannot-step-rnd Hv (estep Hstep) with vlam ← Hv | edet () ← Hstep
  value-cannot-step-rnd Hv (econg (_ , Hctx , refl) Hstep) =
    value-cannot-step-rnd (ctx-value-inv Hctx Hv) Hstep
