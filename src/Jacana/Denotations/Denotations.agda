open import 1Lab.Type.Sigma

open import Cat.Diagram.Exponential
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_∨_) renaming (_⊙_ to _∘_)

open import Jacana.Denotations.Regularity
open import Jacana.Regularity

open import Data.Sum.Base
open import Data.Power using (singleton ; _∪_)

open import Lib.Algebra.Reals
open import Lib.Homotopy.Join renaming (_∗_ to _∨_)
open import Lib.Cat.Concrete
open import Lib.Data.Vector

open import Order.Base

import Jacana.Denotations.Domain as Domain
import Jacana.Denotations.Model as Model
import Jacana.Syntax as Syntax
import Jacana.Typing as Typing

module Jacana.Denotations.Denotations (R : Reals₀) (Ax : RegAssumptions R) where

open Conc-psh.CPSh-on
open RegAssumptions Ax
open VectorSyntax
open Domain R Ax
open Syntax R
open SyntaxVars
open Typing R
open Model R
open Cartesian-closed 𝔇-closed using () renaming ([_,_] to _⇒_)
open Reals R using (ℝ)
open Reg≤

⟨_⟩-sec : Reg↓ → (U : ∫ₚ ⟨_⟩-open-set) → (∣ U .snd ∣ₛ → ℝ) → Type
⟨ c ⟩-sec (r , U) f =
  (r ∈ c × f' ∈ ⟨ r ⟩-reg U (ℝ-open-set 1)) ∨ (f ∈ is-const)
  where
    f' : ∣ U ∣ₛ → ∣ ℝ-open-set {r} 1 ∣ₛ
    f' = ⟨ make ∘ f , _ ⟩

⟨_⟩-sec' : Reg↓ ^ n → (U : ∫ₚ ⟨_⟩-open-set) → (∣ U .snd ∣ₛ → ℝ ^ n) → Type
⟨ cs ⟩-sec' U g = ∀ i → π[ i ] ∘ g ∈ ⟨ π[ i ] cs ⟩-sec U

⟨_∥_⟩-reg : Reg↓ ^ m → Reg↓ ^ n → (ℝ ^ m → ℝ ^ n) → Type
⟨_∥_⟩-reg {m = m} cs cs' f =
  ∀ {U} (g : ∣ U .snd ∣ₛ → ℝ ^ m) → g ∈ ⟨ cs ⟩-sec' U → f ∘ g ∈ ⟨ cs' ⟩-sec' U

⟨_∣_∣_⟩-hom-sec
  : (cs : Reg↓ ^ m) (X : Reg⊆) (cs' : Reg↓ ^ n) (U : ∫ₚ ⟨_⟩-open-set)
  → (∣ U .snd ∣ₛ → ∫ₚ ⟨ cs ∥ cs' ⟩-reg) → Type
⟨_∣_∣_⟩-hom-sec cs X cs' U f =
  □ (Σ[ V ∈ ∫ₚ ⟨_⟩-open-set ] V .fst ∈ X ×
     Σ[ H≤ ∈ U .fst ≤ V .fst ]
     Σ[ g ∈ (∣ U .snd ∣ₛ → ∣ V .snd ∣ₛ) ]
     Σ[ f' ∈ (∣ V .snd ∣ₛ → ∫ₚ ⟨ cs ∥ cs' ⟩-reg) ]
       f ≡ f' ∘ g
     × g ∈ ⟨ U .fst ⟩-reg (U .snd) (⊆-open-set H≤ (V .snd))
     × ∀ {W} {h₁} {h₂}
       → h₁ ∈ ⟨ W .fst ∣ V .fst ⟩-reg (W .snd) (V .snd)
       → h₂ ∈ ⟨ cs ⟩-sec' W
       → uncurry (fst ∘ f') ∘ ⟨ h₁ , h₂ ⟩ ∈ ⟨ cs' ⟩-sec' W)
  ∨ (f ∈ is-const)

record DenotAssumptions : Type where
  -- TODO: Split Prim-reg into explicit cases
  -- TODO: Try to lay out the regularity assumptions in more concrete terms?

  field
    Prim-denot : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ
    Prim-reg
      : ∀ {cs} (Hϕ : PrimTy ϕ ≡ (cs , c)) {U} {gs}
      → gs ∈ ⟨ cs ⟩-sec' U
      → Prim-denot ϕ ∘ gs ∈ ⟨ c ⟩-sec U

    cond-denot : ℝ × ℝ ^ n × ℝ ^ n → ℝ ^ n
    cond-reg
      : ∀ (cs : Reg↓ ^ n) (Hc : ∀ i → P↓ ⊆ cs i) {U g₁ g₂ g₃}
      → g₁ ∈ ⟨ P↓ ⟩-sec U
      → g₂ ∈ ⟨ cs ⟩-sec' U
      → g₃ ∈ ⟨ cs ⟩-sec' U
      → cond-denot ∘ ⟨ g₁ , ⟨ g₂ , g₃ ⟩ ⟩ ∈ ⟨ cs ⟩-sec' U

    diff-denot
      : ∀ m n
        (Hc : (c ≡ A↓ × X ≡ singleton S ∪ singleton A)
            ⊎ (c ≡ S↓ × X ≡ singleton S)
            ⊎ (c ≡ P↓ × X ≡ singleton P))
      → ∫ₚ ⟨ make {n = m} c ∥ make {n = n} c ⟩-reg × ℝ ^ m × ℝ ^ m
      → ℝ ^ n

    diff-reg
      : ∀ m n
        (Hc : (c ≡ A↓ × X ≡ singleton S ∪ singleton A)
            ⊎ (c ≡ S↓ × X ≡ singleton S)
            ⊎ (c ≡ P↓ × X ≡ singleton P))
        {U g₁ g₂ g₃}
      → g₁ ∈ ⟨ make c ∣ singleton P ∣ make c ⟩-hom-sec U
      → g₂ ∈ ⟨ make c ⟩-sec' U
      → g₃ ∈ ⟨ make A↓ ⟩-sec' U
      → diff-denot m n Hc ∘ ⟨ g₁ , ⟨ g₂ , g₃ ⟩ ⟩ ∈ ⟨ make A↓ ⟩-sec' U

    -- TODO: Add the explicit characterization for these properties like above
    solve-denot
      : ∀ n
        (Hc : (c ≡ A↓ × c' ≡ A↓ × X ≡ singleton C ∪ singleton S ∪ singleton A)
            ⊎ (c ≡ C↓ × c' ≡ S↓ × X ≡ singleton S)
            ⊎ (c ≡ C↓ × c' ≡ L↓ × X ≡ singleton C))
      → ⌞ 𝔇ℝ[ c ] ⇒ □⟨ X ⟩₀ (𝔇ℝ'[ make {n = n} c' ] ⇒ 𝔇ℝ'[ make {n = n} c' ]) ⌟ × ℝ ^ (1 + n) × ℝ
      → ℝ ^ (1 + n)

    solve-reg
      : ∀ n
        (Hc : (c ≡ A↓ × c' ≡ A↓ × X ≡ singleton C ∪ singleton S ∪ singleton A)
            ⊎ (c ≡ C↓ × c' ≡ S↓ × X ≡ singleton S)
            ⊎ (c ≡ C↓ × c' ≡ L↓ × X ≡ singleton C))
         {U g₁ g₂ g₃}
      → g₁ ∈ □⟨ X ⟩₀ (𝔇ℝ[ c ] ⇒ □⟨ X ⟩₀ (𝔇ℝ'[ make {n = n} c' ] ⇒ 𝔇ℝ'[ make {n = n} c' ])) .snd .is-sec U
      → g₂ ∈ ⟨ c ∷ make c' ⟩-sec' U
      → g₃ ∈ ⟨ c Reg↓-lat.∩ PL↓ ⟩-sec U
      → solve-denot n Hc ∘ ⟨ g₁ , ⟨ g₂ , g₃ ⟩ ⟩ ∈ ⟨ make A↓ ⟩-sec' U

mk-hom-sec
  : ∀ (cs : Reg↓ ^ m) X (cs' : Reg↓ ^ n) {U f}
  → f ∈ □⟨ X ⟩₀ (𝔇ℝ'[ cs ] ⇒ 𝔇ℝ'[ cs' ]) .snd .is-sec U
  → f ∈ ⟨ cs ∣ X ∣ cs' ⟩-hom-sec U
mk-hom-sec cs X cs' Hf₀ = case Hf₀ of λ where
  (inr H⋆) → inr H⋆
  (inl Hf) → flip (□-elim (λ _ → hlevel 1)) Hf
    λ (W , HW , H≤ , (g , Hg) , (f' , Hf₀') , p) → case Hf₀' of λ Hf' →
    let fac = W , HW , H≤ , g , f' , p , Hg , λ Hh Hh' →
              Hf' _ (inc ((_ , Hh) , refl) , Hh')
    in
    inl (inc fac)


module _ (Ax' : DenotAssumptions) where
  open DenotAssumptions Ax'

  model : Jacana-model _ _
  model .fst = 𝔇
  model .snd = record
    { 𝔇-cartesian = 𝔇-cartesian
    ; 𝔇-closed    = 𝔇-closed
    ; 𝔇-ip        = 𝔇-ip
    ; □⟨_⟩        = □⟨_⟩
    ; □-counit    = □-counit
    ; □-comult    = □-comult-≅
    ; □-⊆         = □-⊆
    ; □-top       = □-top
    ; □-prod      = □-prod-≅
    ; □⟨⊤⟩-Id     = □⟨⊤⟩-Id
    ; 𝔇ℝ[_]       = 𝔇ℝ[_]
    ; □-𝔇ℝ        = □-𝔇ℝ
    ; 𝔇-sub       = 𝔇ℝ-≤
    ; 𝔇-real      = 𝔇ℝ-const
    ; 𝔇-prim      = λ {ϕ} Hϕ → ∫hom (Prim-denot ϕ) λ _ Hg → Prim-reg Hϕ Hg
    ; 𝔇-cond      = λ cs H≤ →
      ∫hom cond-denot λ _ (Hg₁ , Hg₂ , Hg₃) → cond-reg cs H≤ Hg₁ Hg₂ Hg₃
    ; 𝔇-diff = λ {c} m n Hc → ∫hom (diff-denot m n Hc) λ g (Hg₁ , Hg₂ , Hg₃) →
      diff-reg m n Hc
        (mk-hom-sec (make c) (singleton P) (make c) Hg₁)
        Hg₂
        Hg₃
    ; 𝔇-solve = λ {c} n Hc → ∫hom (solve-denot n Hc) λ g (Hg₁ , Hg₂ , Hg₃) →
      solve-reg n Hc Hg₁ Hg₂ Hg₃
    }

  open Denotations model public
