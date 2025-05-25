open import Lib.Reals

module Denotations (R : Reals₀) where

open Reals R hiding (refl)

open import Syntax R
open import Typing R

open import Lib.Prelude hiding (length)
open import Lib.Env

open import Data.List using (length; replicate; lookup)
open import Data.List.Properties using (length-replicate)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_ ; _∷ʳ_ ; ⊆-refl)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)

private
  variable
    Θ Θ′ : List Coeff

record DenotAssumptions : Set₁ where
  field
    𝔉 : (Θ : List Coeff) → Coeff → {{length Θ ≡ n}} → (Vector ℝ n → ℝ) → Set

    𝔉-compose :
      (g : Vector ℝ (length Θ) → Vector ℝ (length Θ′))
      (f : Vector ℝ (length Θ′) → ℝ)
      (_ : ∀ i → 𝔉 Θ (lookup Θ′ i) ((_$ i) ∘ g))
      (_ : 𝔉 Θ′ c f)
      → ----------------------------------------------
      𝔉 Θ c (f ∘ g)

    𝔉-sub :
      (f : Vector ℝ n → ℝ)
      {{_ : length Θ ≡ n}}
      {{_ : length Θ′ ≡ n}}
      (_ : Pointwise _≤′_ Θ Θ′)
      (_ : c′ ≤′ c)
      → -----------------------
      𝔉 Θ c f → 𝔉 Θ′ c′ f

    proj-analytic :
      (i : Fin n) → 𝔉 (replicate n A) A {{length-replicate n}} (_$ i)

module Denotations (Ass : DenotAssumptions) where
  open DenotAssumptions Ass

  ⟦_⟧ᵀ : Type → List Coeff → Set
  ⟦ treal c ⟧ᵀ Θ = ∃ (𝔉 Θ c)
  ⟦ T₁ ⇒[ _ ] T₂ ⟧ᵀ Θ =
    (Θ′ : List Coeff) → Θ ⊆ Θ′ → ⟦ T₁ ⟧ᵀ Θ′ → ⟦ T₂ ⟧ᵀ Θ′
  ⟦ ttup n Ts ⟧ᵀ Θ =
    (i : Fin n) → ⟦ Ts i ⟧ᵀ Θ
  ⟦ tdist T ⟧ᵀ Θ = 𝟙

  ⟦_⟧ᴱ : TyEnv → List Coeff → Set
  ⟦ [] ⟧ᴱ Θ = 𝟙
  ⟦ Γ , _ ∶ T ⟧ᴱ Θ = ⟦ Γ ⟧ᴱ Θ × ⟦ T ⟧ᵀ Θ 


-- abs : ∀ Θ. ⟦ T ⟧ (Θ,c) → ⟦ R[c] → T ⟧Θ

-- abs {R[c′]} f x θ = f (θ,x(θ))
-- abs {T₁ × T₂} (s₁ , s₂) x = (abs {T₁} s₁ x , abs {T₂} s₂ x)
-- abs {T₁ → T₂} (f : ∀ Θ′ ⊇ Θ,x:R[c]. ⟦ T₁ ⟧ Θ′ → ⟦ T₂ ⟧ Θ′) (x : ⟦ R[c] ⟧Θ′) (s : ⟦ T₁ ⟧ Θ″)  (Θ′ ⊇ Θ, Θ″ ⊇ Θ)
--    = let fs : ⟦ T₂ ⟧ (Θ″,c)
--          fs = f (weaken s)
--          absfs : ⟦ R[c] → T ⟧Θ″ (= ∀ Θ ⊇ Θ″. ⟦ R[c] ⟧Θ → ⟦ T ⟧Θ)
--          absfs = abs {T₂} fs
--      in absfs {Θ″ ∪ Θ′} (weaken x)

  app-real-denot : (Θ : List Coeff) → ⟦ treal c ⇒[ e ] T ⟧ᵀ Θ → ⟦ T ⟧ᵀ (c ∷ Θ)
  app-real-denot {c} Θ f = f (c ∷ Θ) (c ∷ʳ ⊆-refl) ((_$ ₀) , projₓ)
    where
      projₓ = 𝔉-sub _ {{length-replicate _}} {!!} {!!} (proj-analytic ₀)


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
