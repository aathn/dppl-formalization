module SmallStep (ℝ : Set) where

open import Syntax ℝ

open import Lib.Prelude
open import Lib.BindingSignature
open import Lib.EvalCtx

open import Data.Vec.Functional using (map)
open import Data.Product using (∃ ; ∃-syntax ; -,_ ; map₁)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)

eval-order : EvalOrder TermSig
eval-order (oabs _) = 0 , λ()
eval-order oif      = 1 , λ { ₀ → ₀ }
eval-order o        = length (TermAr o) , id

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
DetCtx = EvalCtx eval-order Value

RndCtx : Pred (Term × ℝ × List ℝ → Term × ℝ × List ℝ) _
RndCtx E = ∃[ E′ ] DetCtx E′ × E ≗ map₁ E′

record EvalAssumptions : Set where
  field
    0ʳ : ℝ
    _*ʳ_ : ℝ → ℝ → ℝ
    _>ʳ_ : ℝ → ℝ → 𝔹
    PrimEv : (ϕ : Prim) → Vector ℝ (PrimAr ϕ) → ℝ
    ExpectDist : (D : Dist) → Vector ℝ (DistAr D) → ℝ
    AssumeDist : (D : Dist) → Vector ℝ (DistAr D) → ℝ → Term
    ExpectInfer : Term → ℝ
    AssumeInfer : Term → ℝ → Term
    Diff  : Term → Term → Term
    Solve : Term → Term → Term → Term


module Eval (Ass : EvalAssumptions) where
  open EvalAssumptions Ass
  open Subst

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
      : ∀ {n v vs} i
      → v ₀ ≡ tup vs → (∀ j → Value (vs j))
      → -----------------------------------
        proj {n} i v →ᵈ vs i

    eif
      : ∀ {r ts}
      → ts ₀ ≡ real r
      → -------------------------------------------
        if ts →ᵈ (if r >ʳ 0ʳ then ts ₁ else ts ₂)

    ediff
      : ∀ {ts}
      → Value (ts ₀) → Value (ts ₁)
      → -----------------------------
        diff ts →ᵈ Diff (ts ₀) (ts ₁)

    esolve
      : ∀ {ts}
      → Value (ts ₀) → Value (ts ₁) → Value (ts ₂)
      → ------------------------------------------
        solve ts →ᵈ Solve (ts ₀) (ts ₁) (ts ₂)

    eexpectdist
      : ∀ {D rs v}
      → v ₀ ≡ dist D (map real rs)
      → ----------------------------------
        expect v →ᵈ real (ExpectDist D rs)

    eexpectinfer
      : ∀ {v v′}
      → v ₀ ≡ infer v′ → Value (v′ ₀)
      → -------------------------------------
        expect v →ᵈ real (ExpectInfer (v′ ₀))


  data _→ʳ_ : Rel (Term × ℝ × List ℝ) ℓ₀ where

    edet
      : ∀ {t₁ t₂ w s}
      → t₁ →ᵈ t₂
      → (t₁ , w , s) →ʳ (t₂ , w , s)

    eweight
      : ∀ {v r w s}
      → v ₀ ≡ real r
      → -------------------------------------------------------------------
        (weight v , w , s) →ʳ (unit , (if r >ʳ 0ʳ then r *ʳ w else 0ʳ) , s)

    eassumedist
      : ∀ {v D rs w p s}
      → v ₀ ≡ dist D (map real rs)
      → ------------------------------------------------------
        (assume v , w , p :: s) →ʳ (AssumeDist D rs p , w , s)

    eassumeinfer
      : ∀ {v v′ w p s}
      → v ₀ ≡ infer v′ → Value (v′ ₀)
      → ---------------------------------------------------------
        (assume v , w , p :: s) →ʳ (AssumeInfer (v′ ₀) p , w , s)


  -- Full evaluation relations

  _→det_ : Rel Term _
  _→det_ = CongCls _→ᵈ_ DetCtx

  _→rnd_ : Rel (Term × ℝ × List ℝ) _
  _→rnd_ = CongCls _→ʳ_ RndCtx

