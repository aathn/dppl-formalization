open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R hiding (refl)

open import Syntax R
open import Typing R

open import Lib.Prelude hiding (length; _∈_)
open import Lib.Unfinite
open import Lib.Env

open import Data.Fin using (cast)
open import Data.List using (length; lookup; tabulate; replicate; _++_)
open import Data.List.Properties using (length-tabulate ; lookup-tabulate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Unary.All as All using (All ; [] ; _∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.List.Relation.Binary.Sublist.Propositional as SL using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; ⊆-refl ; ⊆-trans)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional as V

private
  variable
    Θ Θ′ : List Coeff

record DenotAssumptions : Set₁ where
  field
    𝔉 : (Θ : List Coeff) → Coeff → {{length Θ ≡ n}} → (ℝ ^ n → ℝ) → Set

    𝔉-const : (r : ℝ) → 𝔉 [] N (const r)

    𝔉-proj : (i : Fin (length Θ)) → 𝔉 Θ (lookup Θ i) π[ i ]

    𝔉-cond :
      𝔉 (P ∷ c ∷ c ∷ []) c
        λ θ → case (θ ₀ ≲? 0ᴿ) λ where
          true  → θ ₁
          false → θ ₂

    𝔉-compose :
      {g : ℝ ^ length Θ → ℝ ^ length Θ′}
      {f : ℝ ^ length Θ′ → ℝ}
      (_ : ∀ i → 𝔉 Θ (lookup Θ′ i) (π[ i ] ∘ g))
      (_ : 𝔉 Θ′ c f)
      → ----------------------------------------
      𝔉 Θ c (f ∘ g)

    𝔉-sub :
      {f : ℝ ^ n → ℝ}
      {{_ : length Θ ≡ n}}
      {{_ : length Θ′ ≡ n}}
      (_ : Pointwise _≤′_ Θ Θ′)
      (_ : c′ ≤′ c)
      → -----------------------
      𝔉 Θ c f → 𝔉 Θ′ c′ f

    𝔉-promote :
      {f : ℝ ^ length Θ → ℝ}
      (_ : All (c′ ≤′_) Θ)
      → --------------------
      𝔉 Θ c f → 𝔉 Θ c′ f

    𝔉-prim :
      {cs : Coeff ^ PrimAr ϕ}
      (_ : PrimTy ϕ ≡ (cs , c))
      → -----------------------
      ∃ (𝔉 (tabulate cs) c)

    𝔉-diff :
      {cs : Coeff ^ n}
      (_ : ∀ i → cs i ≤′ P)
      (_ : ∃ (𝔉 (tabulate cs ++ Θ) c))
      → -----------------------------------------
      ∃ (𝔉 (replicate n A ++ tabulate cs ++ Θ) c)

module Denotations (Ass : DenotAssumptions) where
  open DenotAssumptions Ass

  ⟦_⟧ᵀ : Type → List Coeff → Set
  ⟦ treal c ⟧ᵀ Θ = ∃ (𝔉 Θ c)
  ⟦ T₁ ⇒[ _ ] T₂ ⟧ᵀ Θ = {Θ′ : List Coeff} → Θ ⊆ Θ′ → ⟦ T₁ ⟧ᵀ Θ′ → ⟦ T₂ ⟧ᵀ Θ′
  ⟦ ttup n Ts ⟧ᵀ Θ = (i : Fin n) → ⟦ Ts i ⟧ᵀ Θ
  -- Distributions are interpreted trivially for the time being.
  -- For some reason, wrapping the result in a 1-vector seems
  -- to help the type inference...
  ⟦ tdist T ⟧ᵀ Θ = (i : Fin 1) → ⟦ T ⟧ᵀ Θ

  ⟦_⟧ᴱ : TyEnv → List Coeff → Set
  ⟦ Γ ⟧ᴱ Θ = All (λ (_ , T) → ⟦ T ⟧ᵀ Θ) Γ

  private
    -- A couple of easy lemmas to be used below

    ⊆-lookup : (H⊆ : Θ ⊆ Θ′) (i : Fin (length Θ)) → lookup Θ i ∈ Θ′
    ⊆-lookup H⊆ i = SL.lookup H⊆ (∈-lookup i)

    lookup-tabulate′ :
      {X : Set}
      {xs : X ^ n}
      (i : Fin (length (tabulate xs)))
      → ----------------------------------------------------------
      lookup (tabulate xs) i ≡ π[ cast (length-tabulate xs) i ] xs
    lookup-tabulate′ {n = _+1 n} zero = refl
    lookup-tabulate′ {n = _+1 n} {xs = xs} (succ i) =
      lookup-tabulate′ {xs = V.tail xs} i

  proj-⊆ : {X : Set} → Θ ⊆ Θ′ → X ^ length Θ′ → X ^ length Θ
  proj-⊆ H⊆ xs i = π[ Any.index (⊆-lookup H⊆ i) ] xs

  𝔉-proj-⊆ : (H⊆ : Θ ⊆ Θ′) (i : Fin (length Θ)) → 𝔉 Θ′ (lookup Θ i) (π[ i ] ∘ proj-⊆ H⊆)
  𝔉-proj-⊆ {Θ′ = Θ′} H⊆ i =
    subst (λ c → 𝔉 Θ′ c (π[ i ] ∘ proj-⊆ H⊆))
      (symm $ lookup-index (⊆-lookup H⊆ i)) (𝔉-proj _)

  𝔉-weaken :
    {f : ℝ ^ length Θ → ℝ}
    (H⊆ : Θ ⊆ Θ′)
    → --------------------------------
    𝔉 Θ c f → 𝔉 Θ′ c (f ∘ proj-⊆ H⊆)
  𝔉-weaken H⊆ Hf = 𝔉-compose (𝔉-proj-⊆ H⊆) Hf

  weaken : Θ ⊆ Θ′ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ′
  weaken {T = treal c} H⊆ (_ , Hf) = _ , 𝔉-weaken H⊆ Hf
  weaken {T = T₁ ⇒[ _ ] T₂} H⊆ Hf H⊆′ = Hf (⊆-trans H⊆ H⊆′)
  weaken {T = ttup n Ts} H⊆ Hsem i = weaken H⊆ (Hsem i)
  weaken {T = tdist T} H⊆ Hsem ₀ = weaken H⊆ (Hsem ₀)

  weaken-env : Θ ⊆ Θ′ → ⟦ Γ ⟧ᴱ Θ → ⟦ Γ ⟧ᴱ Θ′
  weaken-env H⊆ = All.map (weaken H⊆)

  abs-real-denot : ⟦ T ⟧ᵀ (c ∷ Θ) → ⟦ treal c ⇒[ e ] T ⟧ᵀ Θ
  abs-real-denot {T = treal c′} f H⊆ (x , Hx)
    with f , Hf ← weaken (refl ∷ H⊆) f = g , Hg
    where
      g = λ θ → f (x θ V.∷ θ)
      Hg = 𝔉-compose (λ { ₀ → Hx ; (succ i) → 𝔉-proj _ }) Hf
  abs-real-denot {T = T₁ ⇒[ _ ] T₂} {c = c} Hf H⊆ (_ , Hx) {Θ′} H⊆′ s =
    abs-real-denot {e = det} fs ⊆-refl (_ , 𝔉-weaken H⊆′ Hx)
    where
      fs : ⟦ T₂ ⟧ᵀ (c ∷ Θ′)
      fs = Hf (refl ∷ ⊆-trans H⊆ H⊆′) (weaken (_ ∷ʳ ⊆-refl) s)
  abs-real-denot {T = ttup n Ts} Hsem H⊆ f i = abs-real-denot {e = det} (Hsem i) H⊆ f
  abs-real-denot {T = tdist T} Hsem H⊆ f _ = abs-real-denot {e = det} (Hsem ₀) H⊆ f

  app-real-denot : ⟦ treal c ⇒[ e ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (c ∷ Θ)
  app-real-denot f = f (_ ∷ʳ ⊆-refl) (π[ ₀ ] , 𝔉-proj ₀)

  abs-real-denot-multi : {cs : Coeff ^ n} → ⟦ T ⟧ᵀ (tabulate cs ++ Θ) → ⟦ treals n cs ⇒[ e ] T ⟧ᵀ Θ
  abs-real-denot-multi = {!!}

  app-real-denot-multi : {cs : Coeff ^ n} → ⟦ treals n cs ⇒[ e ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (tabulate cs ++ Θ)
  app-real-denot-multi = {!!}

  if-denot : ⟦ treal P ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ → ⟦ T ⟧ᵀ Θ
  if-denot {T = treal c} (s , Hs) (s₁ , Hs₁) (s₂ , Hs₂) =
    let g θ = λ {₀ → s θ ; ₁ → s₁ θ ; ₂ → s₂ θ }
        Hg = λ {₀ → Hs ; ₁ → Hs₁ ; ₂ → Hs₂ }
    in
    _ , 𝔉-compose {g = g} Hg 𝔉-cond
  if-denot {T = T₁ ⇒[ _ ] T₂} s s₁ s₂ H⊆ x =
    if-denot (weaken H⊆ s) (s₁ H⊆ x) (s₂ H⊆ x)
  if-denot {T = ttup n Ts} s s₁ s₂ i = if-denot s (s₁ i) (s₂ i)
  if-denot {T = tdist T} s s₁ s₂ _ = if-denot s (s₁ ₀) (s₂ ₀)


  ⟦_⟧ : Γ ⊢ t :[ e ] T → {Θ : List Coeff} → ⟦ Γ ⟧ᴱ Θ → ⟦ T ⟧ᵀ Θ
  ⟦ tvar ⟧ (x ∷ _) = x
  ⟦ tabs (Иi As Habs) ⟧ γ H⊆ s =
    ⟦ Habs (new As) {{unfinite As}} ⟧ (s ∷ weaken-env H⊆ γ)
  ⟦ tapp Hf Ht ⟧ γ = ⟦ Hf ⟧ γ ⊆-refl (⟦ Ht ⟧ γ)
  ⟦ tprim {ϕ = ϕ} {cs = cs} Hϕ _ Htypes ⟧ {Θ} γ =
    _ , 𝔉-compose Hg (𝔉-prim Hϕ .π₂)
    where
      gs : (i : Fin (length (tabulate cs))) → ∃ (𝔉 Θ _)
      gs i = ⟦ Htypes (cast (length-tabulate cs) i) ⟧ γ
      g = λ θ i → gs i . π₁ θ
      Hg = λ i →
        subst (λ c → 𝔉 Θ c (π[ i ] ∘ g))
          (symm (lookup-tabulate′ {xs = cs} i))
          (gs i .π₂)
  ⟦ treal {r = r} ⟧ _ = _ , 𝔉-compose {g = λ _ ()} (λ ()) (𝔉-const r)
  ⟦ ttup _ Htypes ⟧ γ i = ⟦ Htypes i ⟧ γ
  ⟦ tproj i Htype ⟧ γ = ⟦ Htype ⟧ γ i
  ⟦ tif Htype Htype₁ Htype₂ ⟧ γ =
    if-denot (⟦ Htype ⟧ γ) (⟦ Htype₁ ⟧ γ) (⟦ Htype₂ ⟧ γ)
  ⟦ tdiff {n = n} {m} {cs = cs} {ds} H≤ Htype Htype₁ ⟧ γ =
    abs-real-denot-multi {T = treals m ds} {e = det} λ j →
    _ , 𝔉-compose {g = g} {!!} (𝔉-diff H≤ (fapp j) .π₂)
    where
      g = {!!}
      fapp = app-real-denot-multi {e = det} {T = treals m ds} (⟦ Htype ⟧ γ)
  ⟦ tsolve Htype Htype₁ Htype₂ H≤ ⟧ = {!!}
  ⟦ tdist _ _ _ ⟧ = {!!}
  ⟦ tassume Htype ⟧ γ = ⟦ Htype ⟧ γ ₀
  ⟦ tweight Htype ⟧ γ ()
  ⟦ tinfer Htype _ ⟧ γ _ = ⟦ Htype ⟧ γ ⊆-refl λ ()
  ⟦ tweaken Htype x x₁ ⟧ = {!!}
  ⟦ tsub Htype x x₁ ⟧ = {!!}
  ⟦ tpromote Htype x ⟧ = {!!}
