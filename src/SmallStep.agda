module SmallStep (ℝ : Set) where

open import Syntax ℝ

open import Lib.Prelude
open import Lib.BindingSignature
open import Lib.FunExt

open import Function using (_$_ ; const)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Vec.Functional using (fromList ; updateAt ; map)
open import Data.Vec.Functional.Properties using (updateAt-id-local)

data Value : Term → Set where

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
    → Value v
    → ---------------
      Value (infer v)


record EvalAssumptions : Set where
  field
    0ʳ : ℝ
    1ʳ : ℝ
    _*ʳ_ : ℝ → ℝ → ℝ
    _>ʳ_ : ℝ → ℝ → 𝔹
    PrimEv : (ϕ : Prim) → Vector ℝ (PrimAr ϕ) → ℝ
    DistExpect : (D : Dist) → Vector ℝ (DistAr D) → ℝ
    DistAssume : (D : Dist) → Vector ℝ (DistAr D) → ℝ → Term
    Infer : Term → Term
    Expectation : Term → Term
    Diff : Term → Term → Term
    Solve : Term → Term → Term → Term


module Eval (Ass : EvalAssumptions) where
  open EvalAssumptions Ass

  data _→ᵈ_ : Term → Term → Set where
 
    eapp
      : ∀ {T t v}
      → Value v
      → -----------------------------
        app (abs T t) v →ᵈ (0 ≈> v) t
  
    eprim
      : ∀ {ϕ rs}
      → ------------------------------------------ 
        prim ϕ (map real rs) →ᵈ real (PrimEv ϕ rs)
  
    eproj
      : ∀ {n vs} i
      → (∀ j → Value (vs j))
      → ---------------------------
        proj {n} i (tup vs) →ᵈ vs i

    eif
      : ∀ {r t₁ t₂}
      → -------------------------------------------------
        if (real r) t₁ t₂ →ᵈ (if r >ʳ 0ʳ then t₁ else t₂)

    ediff
      : ∀ {v₁ v₂}
      → Value v₁ → Value v₂
      → ------------------------
        diff v₁ v₂ →ᵈ Diff v₁ v₂

    esolve
      : ∀ {v₁ v₂ v₃}
      → Value v₁ → Value v₂ → Value v₃
      → --------------------------------
        solve v₁ v₂ v₃ →ᵈ Solve v₁ v₂ v₃

    eexpectdist
      : ∀ {D rs}
      → -------------------------------------------------------
        expect (dist D (map real rs)) →ᵈ real (DistExpect D rs)

    eexpectinfer
      : ∀ {v}
      → Value v
      → -----------------------------------------
        expect (infer v) →ᵈ Expectation (Infer v)


  data _→ʳ_ : (Term × ℝ × List ℝ) → (Term × ℝ × List ℝ) → Set where
    
    edet
      : ∀ {t₁ t₂ w s}
      → t₁ →ᵈ t₂
      → (t₁ , w , s) →ʳ (t₂ , w , s)

    eweight
      : ∀ {r w s}
      → ------------------------------------------------------
        (weight (real r) , w , s) →ʳ
          ( unit
          , (if r >ʳ 0ʳ and not (r >ʳ 1ʳ) then r *ʳ w else 0ʳ)
          , s
          )

    eassumedist
      : ∀ {D rs w p s}
      → -----------------------------------------------
        (assume (dist D (map real rs)) , w , p :: s) →ʳ
          (DistAssume D rs p , w , s)

    eassumeinfer
      : ∀ {v w p s}
      → Value v
      → ----------------------------------
        (assume (infer v) , w , p :: s) →ʳ
          (app (Infer v) (real p) , w , s)


-- Evaluation contexts and congruence closure

evaluable : (o : TermOp) → Vector 𝔹 (length (TermAr o))
evaluable (oabs _) = const false
evaluable oif      = fromList $ true :: false :: false :: []
evaluable _        = const true

data EvalCtx : (Term → Term) → Set where

  ectx
    : ∀ {o n ts}
    → evaluable o n ≡ true
    → (∀ i → i <ꟳ n → Value (ts i))
    → ----------------------------------------------
      EvalCtx λ t → op (o , updateAt ts n (const t))


data CongCls (_↝_ : Term → Term → Set) : Term → Term → Set where

  estep
    : ∀ {t t′}
    → t ↝ t′
    → ----------------
      CongCls _↝_ t t′

  econg
    : ∀ {E t t′}
    → EvalCtx E
    → CongCls _↝_ t t′
    → ------------------------
      CongCls _↝_ (E t) (E t′)


cong-step
  : ∀ {_↝_ o ts t′} n
  → evaluable o n ≡ true
  → (∀ i → i <ꟳ n → Value (ts i))
  → CongCls _↝_ (ts n) t′
  → -------------------------------------
    ∑ t ∶ _ , CongCls _↝_ (op (o , ts)) t
cong-step {_} {o} {ts} {t′} n Hev Hvs Hstep =
  _ ,
    subst
      (λ ts′ → CongCls _ (op (o , ts′))
                         (op (o , updateAt ts n (const t′))))
      (funext $ updateAt-id-local n ts refl)
      (econg (ectx Hev Hvs) Hstep)
