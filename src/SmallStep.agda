module SmallStep (ℝ 𝕀 : Set) where

open import Syntax ℝ

open import Lib.Prelude
open import Lib.BindingSignature
open import Lib.EvalCtx
open import Lib.Substitution

open import Data.Vec.Functional using (map)
open import Data.Product using (∃ ; ∃-syntax ; map₁)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

instance
  eval-order : EvalOrder TermSig
  eval-order {oabs _} =
    record {len = 0 ; ord = λ() ; inj = λ where {()} }
  eval-order {oif} =
    record {len = 1 ; ord = λ {₀ → ₀} ; inj = λ where {₀} {₀} _ → refl}
  eval-order {o} =
    record {len = length (TermAr o) ; ord = id ; inj = id}

data Value : Pred Term ℓ₀ where

  vabs
    : ∀ {T t}
    → ---------------
      Value (abs T t)

  vreal
    : ∀ {r}
    → --------------
      Value (real r)

  vtup
    : ∀ {n vs}
    → (∀ i → Value (vs i))
    → --------------------
      Value (tup {n} vs)

  vdist
    : ∀ {D vs}
    → (∀ i → Value (vs i))
    → --------------------
      Value (dist D vs)

  vinfer
    : ∀ {v}
    → Value (v ₀)
    → ---------------
      Value (infer v)


DetCtx : Pred (Term → Term) _
DetCtx = EvalCtx Value

RndCtx : Pred (Term × ℝ × List 𝕀 → Term × ℝ × List 𝕀) _
RndCtx E = ∃[ E′ ] DetCtx E′ × E ≡ map₁ E′

record EvalAssumptions : Set where
  field
    0ʳ : ℝ
    _*ʳ_ : ℝ → ℝ → ℝ
    _>ʳ_ : ℝ → ℝ → 𝔹
    PrimEv : (ϕ : Prim) → Vector ℝ (PrimAr ϕ) → ℝ
    Sample : (D : Dist) → Vector ℝ (DistAr D) → 𝕀 → ∃ Value
    Infer  : ∃ Value → 𝕀 → ∃ Value
    Expect : (𝕀 → ∃ Value) → ℝ
    Diff  : ∃ Value → ∃ Value → Term
    Solve : ∃ Value → ∃ Value → ∃ Value → Term


module Eval (Ass : EvalAssumptions) where
  open EvalAssumptions Ass

  data _→ᵈ_ : Rel Term ℓ₀ where
 
    eapp
      : ∀ {ts T t}
      → ts ₀ ≡ abs T t → Value (ts ₁)
      → -----------------------------
        app ts →ᵈ (0 ≈> ts ₁) (t ₀)
  
    eprim
      : ∀ {ϕ vs rs}
      → vs ≡ map real rs
      → -------------------------------
        prim ϕ vs →ᵈ real (PrimEv ϕ rs)
  
    eproj
      : ∀ {n t ts} i
      → t ₀ ≡ tup ts → (∀ j → Value (ts j))
      → -----------------------------------
        proj {n} i t →ᵈ ts i

    eif
      : ∀ {r ts}
      → ts ₀ ≡ real r
      → -------------------------------------------
        if ts →ᵈ (if r >ʳ 0ʳ then ts ₁ else ts ₂)

    ediff
      : ∀ {ts}
      → (v₀ : Value (ts ₀)) (v₁ : Value (ts ₁))
      → ---------------------------------------
        diff ts →ᵈ Diff (_ , v₀) (_ , v₁)

    esolve
      : ∀ {ts}
      → (v₀ : Value (ts ₀)) (v₁ : Value (ts ₁)) (v₂ : Value (ts ₂))
      → -----------------------------------------------------------
        solve ts →ᵈ Solve (_ , v₀) (_ , v₁) (_ , v₂)

    eexpectdist
      : ∀ {D rs t}
      → t ₀ ≡ dist D (map real rs)
      → ---------------------------------------
        expect t →ᵈ real (Expect (Sample D rs))

    eexpectinfer
      : ∀ {t t′}
      → t ₀ ≡ infer t′ → (v : Value (t′ ₀))
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
      → -------------------------------------------------------------------
        (weight t , w , s) →ʳ (unit , (if r >ʳ 0ʳ then r *ʳ w else 0ʳ) , s)

    eassumedist
      : ∀ {t D rs w p s}
      → t ₀ ≡ dist D (map real rs)
      → ------------------------------------------------------
        (assume t , w , p :: s) →ʳ (Sample D rs p .π₁ , w , s)

    eassumeinfer
      : ∀ {t t′ w p s}
      → t ₀ ≡ infer t′ → (v : Value (t′ ₀))
      → ---------------------------------------------------------
        (assume t , w , p :: s) →ʳ (Infer (_ , v) p .π₁ , w , s)


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
