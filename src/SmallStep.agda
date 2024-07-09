module SmallStep (ℝ : Set) where

open import Syntax ℝ

open import Lib.Prelude
open import Lib.BindingSignature

open import Function using (_$_ ; const)
open import Data.Fin using () renaming (_<_ to _<ꟳ_)
open import Data.Vec.Functional using (fromList ; updateAt ; map)

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


data CongCls
  {A B : Set} (_↝_ : A → A → Set) (F : Term → B → A)
  : A → A → Set
  where

  estep
    : ∀ {a b}
    → a ↝ b
    → -----------------
      CongCls _↝_ F a b

  econg
    : ∀ {E t a t′ b}
    → EvalCtx E
    → CongCls _↝_ F (F t a) (F t′ b)
    → --------------------------------------
      CongCls _↝_ F (F (E t) a) (F (E t′) b)


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
  open Subst {TermSig}

  data _→ᵈ_ : Term → Term → Set where
 
    eapp
      : ∀ {ts T t}
      → ts 0ꟳ ≡ abs T t
      → Value (ts 1ꟳ)
      → ------------------------
        app ts →ᵈ (0 ≈> ts 1ꟳ) t
  
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
      : ∀ {ts r}
      → ts 0ꟳ ≡ real r
      → -------------------------------------------
        if ts →ᵈ (if r >ʳ 0ʳ then ts 1ꟳ else ts 2ꟳ)

    ediff
      : ∀ {ts}
      → Value (ts 0ꟳ) → Value (ts 1ꟳ)
      → -------------------------------
        diff ts →ᵈ Diff (ts 0ꟳ) (ts 1ꟳ)

    esolve
      : ∀ {ts}
      → Value (ts 0ꟳ) → Value (ts 1ꟳ) → Value (ts 2ꟳ)
      → ---------------------------------------------
        solve ts →ᵈ Solve (ts 0ꟳ) (ts 1ꟳ) (ts 2ꟳ)

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
          (app (tup₂ (Infer v) (real p)) , w , s)


  -- Full evaluation relations

  _→det_ : Term → Term → Set
  _→det_ = CongCls {B = 𝟙} _→ᵈ_ const

  _→rnd_ : (Term × ℝ × List ℝ) → (Term × ℝ × List ℝ) → Set
  _→rnd_ = CongCls _→ʳ_ (λ t ws → t , ws)

