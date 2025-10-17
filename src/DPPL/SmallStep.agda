open import Lib.Algebra.Reals

module DPPL.SmallStep (R : Reals₀) where

open Reals R
open Interval R

open import DPPL.Syntax R

open import Lib.Prelude hiding (_*_)
open import Lib.Data.Vector
open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.EvalCtx
open import Lib.Syntax.Substitution

open SyntaxVars
open ListSyntax

instance
  eval-order : EvalOrder TmSig
  eval-order {lam _} = record
    { len = 0 ; ord = λ() ; inj = λ where {()} }
  eval-order {if} = record
    { len = 1
    ; ord = lookup (₀ ∷ [])
    ; inj = λ {x} {y} _ →
      case fin-view x of λ { zero →
      case fin-view y of λ { zero → refl }}
    }
    where open VecSyntax
  eval-order {o} = record
    { len = length (TmAr o) ; ord = id ; inj = id }

data IsValue : Tm → Type where

  vabs :
    {t : Vector Tm 1}
    → -----------------
    IsValue (lam T ▸ t)

  vreal : IsValue (real r)

  vtup :
    {vs : Vector Tm n}
    (_ : ∀ i → IsValue (vs i))
    → ------------------------
    IsValue (tup n ▸ vs)

  vinfer :
    {v : Vector Tm 1}
    (_ : IsValue (v ₀))
    → -----------------
    IsValue (infer ▸ v)

Value : Type
Value = Σ _ IsValue

DetCtx : (Tm → Tm) → Type
DetCtx = EvalCtx IsValue

RndCtx : (Tm × ℝ × List 𝕀 → Tm × ℝ × List 𝕀) → Type
RndCtx E = Σ _ λ E' → DetCtx E' × E ≡ λ (x , y) → (E' x , y)

record EvalAssumptions : Type where
  field
    is-pos : ℝ → Bool
    PrimEv : (ϕ : Prim) → Vector ℝ (PrimAr ϕ) → ℝ
    Infer  : Value → 𝕀 → Value
    Diff  : Value → Value → Tm
    Solve : Value → Value → Value → Tm

module Eval (Ax : EvalAssumptions) where
  open EvalAssumptions Ax

  data _→ᵈ_ : Tm → Tm → Type where
 
    eapp :
      {ts : Vector Tm 2}
      {t : Vector Tm 1}
      (_ : ts ₀ ≡ lam T ▸ t)
      (_ : IsValue (ts ₁))
      → ---------------------------
      app ▸ ts →ᵈ (0 ≈> ts ₁) (t ₀)
  
    eprim :
      {t : Tm ^ 1}
      {rs : ℝ  ^ PrimAr ϕ}
      (_ : t ₀ ≡ tup _ ▸ λ i → real (rs i))
      → -----------------------------------
      prim ϕ ▸ t →ᵈ real (PrimEv ϕ rs)
  
    eproj :
      {ts : Tm ^ n}
      {t  : Tm ^ 1}
      (i : Fin n)
      (_ : t ₀ ≡ tup n ▸ ts)
      (_ : ∀ j → IsValue (ts j))
      → ------------------------
      proj n i ▸ t →ᵈ ts i

    eif :
      {ts : Tm ^ 3}
      (_ : ts ₀ ≡ real r)
      → ------------------------------------------
      if ▸ ts →ᵈ (if is-pos r then ts ₁ else ts ₂)

    ediff :
      {ts : Tm ^ 2}
      (v₀ : IsValue (ts ₀))
      (v₁ : IsValue (ts ₁))
      → ---------------------------------
      diff ▸ ts →ᵈ Diff (_ , v₀) (_ , v₁)

    esolve :
      {ts : Tm ^ 3}
      (v₀ : IsValue (ts ₀))
      (v₁ : IsValue (ts ₁))
      (v₂ : IsValue (ts ₂))
      → --------------------------------------------
      solve ▸ ts →ᵈ Solve (_ , v₀) (_ , v₁) (_ , v₂)

  module EvalVars where
    variable
      w : ℝ
      p : 𝕀
      s : List 𝕀

  open EvalVars

  data _→ʳ_ : (Tm × ℝ × List 𝕀) → (Tm × ℝ × List 𝕀) → Type where

    edet :
      {t₁ t₂ : Tm}
      (_ : t₁ →ᵈ t₂)
      → --------------------------
      (t₁ , w , s) →ʳ (t₂ , w , s)

    eweight :
      {t : Vector Tm 1}
      (_ : t ₀ ≡ real r)
      → ------------------------------------------------------------------
      (weight ▸ t , w , s) →ʳ (unit , (if is-pos r then r * w else 0r) , s)

    euniform : (uniform , w , p ∷ s) →ʳ (real (p .fst) , w , s)

    esample :
      {t t' : Vector Tm 1}
      (_ : t ₀ ≡ infer ▸ t')
      (v : IsValue (t' ₀))
      → -------------------------------------------------------
      (sample ▸ t , w , p ∷ s) →ʳ (Infer (_ , v) p .fst , w , s)


  -- Full evaluation relations

  _→det_ : Tm → Tm → Type
  _→det_ = CongCls _→ᵈ_ DetCtx

  _→rnd_ : (Tm × ℝ × List 𝕀) → (Tm × ℝ × List 𝕀) → Type
  _→rnd_ = CongCls _→ʳ_ RndCtx

  -- Multi-step relations

  -- _→det*_ : Tm → Tm → Type
  -- _→det*_ = Star _→det_

  -- _→rnd*_ : (Tm × ℝ × List 𝕀) → (Tm × ℝ × List 𝕀) → Type
  -- _→rnd*_ = Star _→rnd_
