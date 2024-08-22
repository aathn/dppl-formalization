open import Lib.Reals

module SmallStep (R : Reals₀) where
open Reals R hiding (refl)
open Interval R

open import Syntax R

open import Lib.Prelude
open import Lib.BindingSignature
open import Lib.EvalCtx
open import Lib.Substitution

open import Data.Vec.Functional using (map)
open import Data.Product using (map₁)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

instance
  eval-order : EvalOrder TermSig
  eval-order {olam _} =
    record {len = 0 ; ord = λ() ; inj = λ where {()} }
  eval-order {oif} =
    record {len = 1 ; ord = λ {₀ → ₀} ; inj = λ where {₀} {₀} _ → refl}
  eval-order {o} =
    record {len = length (TermAr o) ; ord = id ; inj = id}

data IsValue : Pred Term ℓ₀ where

  vlam
    : ∀ {T t}
    → ---------------
      IsValue (lam T t)

  vreal
    : ∀ {r}
    → --------------
      IsValue (real r)

  vtup
    : ∀ {n vs}
    → (∀ i → IsValue (vs i))
    → --------------------
      IsValue (tup {n} vs)

  vdist
    : ∀ {D vs}
    → (∀ i → IsValue (vs i))
    → --------------------
      IsValue (dist D vs)

  vinfer
    : ∀ {v}
    → IsValue (v ₀)
    → ---------------
      IsValue (infer v)

Value : Set
Value = ∃ IsValue

DetCtx : Pred (Term → Term) _
DetCtx = EvalCtx IsValue

RndCtx : Pred (Term × ℝ × List 𝕀 → Term × ℝ × List 𝕀) _
RndCtx E = ∃ λ E′ → DetCtx E′ × E ≡ map₁ E′

record EvalAssumptions : Set where
  field
    PrimEv : (ϕ : Prim) → Vector ℝ (PrimAr ϕ) → ℝ
    Sample : (D : Dist) → Vector ℝ (DistAr D) → 𝕀 → Value
    Infer  : Value → 𝕀 → Value
    Expect : (𝕀 → Value) → ℝ
    Diff  : Value → Value → Term
    Solve : Value → Value → Value → Term


module Eval (Ass : EvalAssumptions) where
  open EvalAssumptions Ass

  data _→ᵈ_ : Rel Term ℓ₀ where
 
    eapp
      : ∀ {ts T t}
      → ts ₀ ≡ lam T t → IsValue (ts ₁)
      → -----------------------------
        app ts →ᵈ (0 ≈> ts ₁) (t ₀)
  
    eprim
      : ∀ {ϕ vs rs}
      → vs ≡ map real rs
      → -------------------------------
        prim ϕ vs →ᵈ real (PrimEv ϕ rs)
  
    eproj
      : ∀ {n t ts} i
      → t ₀ ≡ tup ts → (∀ j → IsValue (ts j))
      → -----------------------------------
        proj {n} i t →ᵈ ts i

    eif
      : ∀ {r ts}
      → ts ₀ ≡ real r
      → ------------------------------------------
        if ts →ᵈ (if r ≲? 0ᴿ then ts ₂ else ts ₁)

    ediff
      : ∀ {ts}
      → (v₀ : IsValue (ts ₀)) (v₁ : IsValue (ts ₁))
      → ---------------------------------------
        diff ts →ᵈ Diff (_ , v₀) (_ , v₁)

    esolve
      : ∀ {ts}
      → (v₀ : IsValue (ts ₀)) (v₁ : IsValue (ts ₁)) (v₂ : IsValue (ts ₂))
      → -----------------------------------------------------------
        solve ts →ᵈ Solve (_ , v₀) (_ , v₁) (_ , v₂)

    eexpectdist
      : ∀ {D rs t}
      → t ₀ ≡ dist D (map real rs)
      → ---------------------------------------
        expect t →ᵈ real (Expect (Sample D rs))

    eexpectinfer
      : ∀ {t t′}
      → t ₀ ≡ infer t′ → (v : IsValue (t′ ₀))
      → -----------------------------------------
        expect t →ᵈ real (Expect (Infer (_ , v)))


  data _→ʳ_ : Rel (Term × ℝ × List 𝕀) ℓ₀ where

    edet
      : ∀ {t₁ t₂ w s}
      → t₁ →ᵈ t₂
      → (t₁ , w , s) →ʳ (t₂ , w , s)

    eweight
      : ∀ {t r w s}
      → t ₀ ≡ real r
      → --------------------------------------------------------------------
        (weight t , w , s) →ʳ (unit , (if r ≲? 0ᴿ then 0ᴿ else r * w) , s)

    eassumedist
      : ∀ {t D rs w p s}
      → t ₀ ≡ dist D (map real rs)
      → ------------------------------------------------------
        (assume t , w , p ∷ s) →ʳ (Sample D rs p .π₁ , w , s)

    eassumeinfer
      : ∀ {t t′ w p s}
      → t ₀ ≡ infer t′ → (v : IsValue (t′ ₀))
      → ---------------------------------------------------------
        (assume t , w , p ∷ s) →ʳ (Infer (_ , v) p .π₁ , w , s)


  -- Full evaluation relations

  _→det_ : Rel Term _
  _→det_ = CongCls _→ᵈ_ DetCtx

  _→rnd_ : Rel (Term × ℝ × List 𝕀) _
  _→rnd_ = CongCls _→ʳ_ RndCtx

  -- Multi-step relations

  _→det*_ : Rel Term _
  _→det*_ = Star _→det_

  _→rnd*_ : Rel (Term × ℝ × List 𝕀) _
  _→rnd*_ = Star _→rnd_
