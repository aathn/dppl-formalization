open import Cat.Functor.Properties
open import Cat.Prelude

open import Data.Nat.Base using (H-Level-≤)

open import Jacana.Denotations.Regularity
open import Jacana.Regularity

open import Lib.Algebra.Reals
open import Lib.Homotopy.Join
open import Lib.Cat.Concrete
open import Lib.Data.Vector

open import Order.Base

module Jacana.Denotations.Site (R : Reals₀) (Ax : RegAssumptions R) where

open RegAssumptions Ax
open Reals R using (ℝ)

open Reg≤

ℛ : Precategory lzero lzero
ℛ .Precategory.Ob                    = ∫ₚ ⟨_⟩-open-set
ℛ .Precategory.Hom (c , U) (d , V)   = ∫ₚ (⟨ c ∣ d ⟩-reg U V)
ℛ .Precategory.Hom-set _ _ _ _       = hlevel 1
ℛ .Precategory.id {c , U}            = (λ x → x) , id-reg'
ℛ .Precategory._∘_ (f , Hf) (g , Hg) = f ⊙ g , ∘-reg' Hf Hg
ℛ .Precategory.idr f                 = Σ-prop-path! refl
ℛ .Precategory.idl g                 = Σ-prop-path! refl
ℛ .Precategory.assoc f g h           = Σ-prop-path! refl

module ℛ = Precategory ℛ

ℛ-underlying : Functor ℛ (Sets _)
ℛ-underlying .Functor.F₀ (_ , U) = el! ∣ U ∣ₛ
ℛ-underlying .Functor.F₁ f       = f .fst
ℛ-underlying .Functor.F-id       = refl
ℛ-underlying .Functor.F-∘ _ _    = refl

ℛ-faithful : is-faithful ℛ-underlying
ℛ-faithful = Σ-prop-path!

ℛ-conc : Conc-category _ ℛ
ℛ-conc .Conc-category.underlying          = ℛ-underlying
ℛ-conc .Conc-category.underlying-faithful = ℛ-faithful

open Conc-category ℛ-conc

ℛ-id≤ : ∀ {c c'} {U} (H≤ : c ≤ c') → ℛ.Hom (c , ⊆-open-set H≤ U) (c' , U)
ℛ-id≤ H≤ = (λ x → x) , inl (H≤ , id-reg)

ℛ-const : ∀ {c c' U V} → ∣ V ∣ₛ → ℛ.Hom (c , U) (c' , V)
ℛ-const x = (λ _ → x) , const-reg' x
