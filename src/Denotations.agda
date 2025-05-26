open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R hiding (refl)

open import Syntax R
open import Typing R

open import Lib.Prelude hiding (length; _^_; _∈_)
open import Lib.Env

open import Data.List using (length; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.List.Relation.Binary.Sublist.Propositional as SL using (_⊆_ ; [] ; _∷_ ; _∷ʳ_ ; ⊆-refl ; ⊆-trans)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional as V

private
  variable
    Θ Θ′ : List Coeff

_^_ : Set → ℕ → Set
X ^ n = Vector X n

pr : {X : Set}{n : ℕ} (i : Fin n) → X ^ n → X
pr i = _$ i

record DenotAssumptions : Set₁ where
  field
    𝔉 : (Θ : List Coeff) → Coeff → {{length Θ ≡ n}} → (ℝ ^ n → ℝ) → Set

    𝔉-proj : (i : Fin (length Θ)) → 𝔉 Θ (lookup Θ i) (pr i)

    𝔉-compose :
      {g : ℝ ^ length Θ → ℝ ^ length Θ′}
      {f : ℝ ^ length Θ′ → ℝ}
      (_ : ∀ i → 𝔉 Θ (lookup Θ′ i) (pr i ∘ g))
      (_ : 𝔉 Θ′ c f)
      → --------------------------------------
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


module Denotations (Ass : DenotAssumptions) where
  open DenotAssumptions Ass

  ⟦_⟧ᵀ : Type → List Coeff → Set
  ⟦ treal c ⟧ᵀ Θ = ∃ (𝔉 Θ c)
  ⟦ T₁ ⇒[ _ ] T₂ ⟧ᵀ Θ = {Θ′ : List Coeff} → Θ ⊆ Θ′ → ⟦ T₁ ⟧ᵀ Θ′ → ⟦ T₂ ⟧ᵀ Θ′
  ⟦ ttup n Ts ⟧ᵀ Θ = (i : Fin n) → ⟦ Ts i ⟧ᵀ Θ
  ⟦ tdist T ⟧ᵀ Θ = 𝟙

  ⟦_⟧ᴱ : TyEnv → List Coeff → Set
  ⟦ [] ⟧ᴱ Θ = 𝟙
  ⟦ Γ , _ ∶ T ⟧ᴱ Θ = ⟦ Γ ⟧ᴱ Θ × ⟦ T ⟧ᵀ Θ 

  private
    ⊆-lookup : (H⊆ : Θ ⊆ Θ′) (i : Fin (length Θ)) → lookup Θ i ∈ Θ′
    ⊆-lookup H⊆ i = SL.lookup H⊆ (∈-lookup i)

  proj-⊆ : {X : Set} → Θ ⊆ Θ′ → X ^ length Θ′ → X ^ length Θ
  proj-⊆ H⊆ xs i = pr (Any.index (⊆-lookup H⊆ i)) xs

  𝔉-proj-⊆ : (H⊆ : Θ ⊆ Θ′) (i : Fin (length Θ)) → 𝔉 Θ′ (lookup Θ i) (pr i ∘ proj-⊆ H⊆)
  𝔉-proj-⊆ {Θ′ = Θ′} H⊆ i =
    subst (λ c → 𝔉 Θ′ c (pr i ∘ proj-⊆ H⊆))
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
  weaken {T = ttup n x} H⊆ Hsem = weaken H⊆ ∘ Hsem
  weaken {T = tdist T} = λ _ _ → tt

  abs-real-denot : ⟦ T ⟧ᵀ (c ∷ Θ) → ⟦ treal c ⇒[ e ] T ⟧ᵀ Θ
  abs-real-denot {T = treal c′} f H⊆ (x , Hx)
    with f , Hf ← weaken (refl ∷ H⊆) f = g , Hg
    where
      g = λ θ → f (x θ V.∷ θ)
      Hg = 𝔉-compose (λ { ₀ → Hx ; (succ i) → 𝔉-proj _ }) Hf
  abs-real-denot {T = T₁ ⇒[ _ ] T₂} {c = c} Hf H⊆ (_ , Hx) {Θ′} H⊆′ s =
    let fs : ⟦ T₂ ⟧ᵀ (c ∷ Θ′)
        fs = Hf (refl ∷ ⊆-trans H⊆ H⊆′) (weaken (_ ∷ʳ ⊆-refl) s)
    in
    abs-real-denot {e = det} fs ⊆-refl (_ , 𝔉-weaken H⊆′ Hx)
  abs-real-denot {T = ttup n Ts} Hsem H⊆ f i = abs-real-denot {e = det} (Hsem i) H⊆ f
  abs-real-denot {T = tdist T} = λ _ _ _ → tt

  app-real-denot : ⟦ treal c ⇒[ e ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (c ∷ Θ)
  app-real-denot f = f (_ ∷ʳ ⊆-refl) (pr ₀ , 𝔉-proj ₀)


  ⟦_⟧ : Γ ⊢ t :[ det ] T → (Θ : List Coeff) → ⟦ Γ ⟧ᴱ Θ → ⟦ T ⟧ᵀ Θ
  ⟦ tvar ⟧ Θ (_ , x) = x
  ⟦ tabs x ⟧ = {!!}
  ⟦ tapp Htype Htype₁ ⟧ = {!!}
  ⟦ tprim x x₁ x₂ ⟧ = {!!}
  ⟦ treal ⟧ = {!!}
  ⟦ ttup x x₁ ⟧ = {!!}
  ⟦ tproj i Htype ⟧ = {!!}
  ⟦ tif Htype Htype₁ Htype₂ ⟧ = {!!}
  ⟦ tdiff x Htype Htype₁ ⟧ = {!!}
  ⟦ tsolve Htype Htype₁ Htype₂ x ⟧ = {!!}
  ⟦ tdist _ _ _ ⟧ = λ Θ _ → tt
  ⟦ tinfer _ _ ⟧ = λ Θ _ → tt
  ⟦ tweaken Htype x x₁ ⟧ = {!!}
  ⟦ tsub Htype x x₁ ⟧ = {!!}
  ⟦ tpromote Htype x ⟧ = {!!}
